// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

import (
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"slices"
	"strings"
	"time"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// Scaling reports its sweeps under one mapping, a key for each, in the order
// of scalingResults' fields, which is the sweep order benchmarks/SCHEMA.yaml
// pins across the four bindings. The schema holds each row to its key set,
// compared as a set.
type traceSizeRow struct {
	Frames   int     `json:"frames"`
	FPS      float64 `json:"fps"`
	Relative float64 `json:"relative"`
}

type propCountRow struct {
	Properties int     `json:"properties"`
	FPS        float64 `json:"fps"`
	USPerFrame float64 `json:"us_per_frame"`
	Relative   float64 `json:"relative"`
}

type complexityRow struct {
	Complexity string  `json:"complexity"`
	FPS        float64 `json:"fps"`
	USPerFrame float64 `json:"us_per_frame"`
	Relative   float64 `json:"relative"`
}

type dbcSizeRow struct {
	Messages       int     `json:"messages"`
	Seconds        float64 `json:"seconds"`
	AllocatedBytes uint64  `json:"allocated_bytes"`
	MessagesPerSec float64 `json:"messages_per_sec"`
	Relative       float64 `json:"relative"`
}

type literalLengthRow struct {
	Digits         int     `json:"digits"`
	Seconds        float64 `json:"seconds"`
	AllocatedBytes uint64  `json:"allocated_bytes"`
	DigitsPerSec   float64 `json:"digits_per_sec"`
	Relative       float64 `json:"relative"`
}

type scalingResults struct {
	TraceSizeCAN20     []traceSizeRow     `json:"trace_size_can20"`
	TraceSizeCANFD     []traceSizeRow     `json:"trace_size_canfd"`
	PropertyCount      []propCountRow     `json:"property_count"`
	PropertyComplexity []complexityRow    `json:"property_complexity"`
	DBCSize            []dbcSizeRow       `json:"dbc_size"`
	TextLiteralLength  []literalLengthRow `json:"text_literal_length"`
	JSONLiteralLength  []literalLengthRow `json:"json_literal_length"`
}

// alwaysBetween, alwaysLessThan and alwaysLessThanRat build the Always-wrapped
// atomic predicates the scaling sweeps share. The signals and bounds are the
// ones python/benchmarks/scaling.py sweeps, so the two harnesses measure the
// same properties.
func alwaysBetween(sig string, lo, hi int64) aletheia.Formula {
	return aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.Between{Signal: aletheia.SignalName(sig), Min: aletheia.IntRational(lo), Max: aletheia.IntRational(hi)}}}
}

func alwaysLessThan(sig string, v int64) aletheia.Formula {
	return alwaysLessThanRat(sig, v, 1)
}

func alwaysLessThanRat(sig string, num, den int64) aletheia.Formula {
	return aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: aletheia.SignalName(sig), Value: rat(num, den)}}}
}

// propertyTemplates are the ten the property-count sweep cycles through.
func propertyTemplates() []aletheia.Formula {
	return []aletheia.Formula{
		alwaysBetween("EngineSpeed", 0, 8000),
		alwaysBetween("EngineTemp", -40, 215),
		alwaysLessThanRat("BrakePressure", 13107, 2),
		alwaysLessThan("EngineSpeed", 7000),
		alwaysLessThan("EngineTemp", 200),
		alwaysLessThan("BrakePressure", 5000),
		alwaysBetween("EngineSpeed", 500, 7500),
		alwaysBetween("EngineTemp", -20, 180),
		alwaysBetween("BrakePressure", 0, 4000),
		alwaysLessThan("EngineSpeed", 6000),
	}
}

func makeProperties(count int) []aletheia.Formula {
	templates := propertyTemplates()
	props := make([]aletheia.Formula, count)
	for i := 0; i < count; i++ {
		props[i] = templates[i%len(templates)]
	}
	return props
}

// meanFPS averages streaming fps over numRuns passes. Averaging is the
// methodology all four bindings share: noise on an un-averaged baseline would
// multiply into every relative value in the sweep.
func meanFPS(backend *aletheia.FFIBackend, f frameFamily, props []aletheia.Formula, numFrames, numRuns int) float64 {
	fpsList := make([]float64, 0, numRuns)
	for r := 0; r < numRuns; r++ {
		fps, err := benchmarkStreaming(backend, f, props, numFrames)
		if err != nil {
			die("scaling point (%d frames) run %d/%d failed: %v", numFrames, r+1, numRuns, err)
		}
		fpsList = append(fpsList, fps)
	}
	return mean(fpsList)
}

func traceSizes(quick bool) []int {
	if quick {
		return []int{1000, 5000, 10000, 50000}
	}
	return []int{1000, 5000, 10000, 50000, 100000}
}

// complexityLevels are the five labelled bundles the complexity sweep measures,
// in the order benchmarks/SCHEMA.yaml spells them.
func complexityLevels() []struct {
	label string
	props []aletheia.Formula
} {
	// Implies is not a primitive: it lowers to Or(Not(antecedent), consequent),
	// which is what makes this bundle a complexity step rather than a rename.
	implication := aletheia.Always{Inner: aletheia.Implies(
		aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "EngineSpeed", Value: aletheia.IntRational(1000)}},
		aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "EngineTemp", Value: aletheia.IntRational(100)}},
	)}
	engineSpeed := alwaysBetween("EngineSpeed", 0, 8000)
	engineTemp := alwaysBetween("EngineTemp", -40, 215)
	brakeHalf := alwaysLessThanRat("BrakePressure", 13107, 2)
	return []struct {
		label string
		props []aletheia.Formula
	}{
		{"Simple predicate", []aletheia.Formula{alwaysLessThan("EngineSpeed", 8000)}},
		{"Range predicate", []aletheia.Formula{engineSpeed}},
		{"Two predicates (AND)", []aletheia.Formula{engineSpeed, engineTemp}},
		{"Three predicates", []aletheia.Formula{engineSpeed, engineTemp, brakeHalf}},
		{"Implication", []aletheia.Formula{implication}},
	}
}

// dbcSizeDBC is the definition the DBC-size sweep loads: n extended-ID
// messages of one byte-wide signal each, no two sharing an ID, a message name
// or a signal name, with every kind of reference growing with n. Message i is
// sent by node N{i}, with N{(i+1) mod n} as its one additional sender, and its
// signal is received by N{i}; the nodes are N0 to N{n-1}, and each message
// carries one comment naming it by its CAN ID. Every name resolves, so every
// load succeeds.
func dbcSizeDBC(n int) aletheia.DBCDefinition {
	node := func(i int) aletheia.NodeName { return aletheia.NodeName(fmt.Sprintf("N%d", i)) }
	msgs := make([]aletheia.DBCMessage, 0, n)
	nodes := make([]aletheia.DBCNode, 0, n)
	comments := make([]aletheia.DBCComment, 0, n)
	for i := 0; i < n; i++ {
		id := mustExtID(0x100000 + uint32(i))
		sig := aletheia.DBCSignal{Name: aletheia.SignalName(fmt.Sprintf("S%d", i)), StartBit: 0, BitLength: 8, ByteOrder: aletheia.LittleEndian, IsSigned: false,
			Factor: rat(1, 1), Offset: rat(0, 1), Minimum: rat(0, 1), Maximum: rat(255, 1), Unit: "", Presence: aletheia.AlwaysPresent{},
			Receivers: []aletheia.NodeName{node(i)}}
		msgs = append(msgs, aletheia.NewDBCMessage(id, aletheia.MessageName(fmt.Sprintf("M%d", i)), mustDLC(8), node(i), []aletheia.NodeName{node((i + 1) % n)}, []aletheia.DBCSignal{sig}))
		nodes = append(nodes, aletheia.DBCNode{Name: node(i)})
		comments = append(comments, aletheia.DBCComment{Target: aletheia.DBCCommentTargetMessage{ID: id}, Text: "c"})
	}
	d := aletheia.NewDBCDefinition("1.0", msgs)
	d.Nodes = nodes
	d.Comments = comments
	return *d
}

func dbcSizes(quick bool) []int {
	if quick {
		return []int{2500, 5000, 10000}
	}
	return []int{1250, 2500, 5000, 10000}
}

// literalLengthText is the DBC text the text literal sweep loads: one
// message whose one signal's factor is written as 1. followed by that many
// zeros, which the kernel reduces to 1, so every load succeeds and only the
// literal's length grows.
func literalLengthText(digits int) string {
	return "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 200 Msg: 8 ECU\n" +
		" SG_ Sel : 0|8@1+ (1." + strings.Repeat("0", digits) + ",0) [0|255] \"\" ECU\n"
}

// literalLengthCommand is literalLengthText's DBC as the parseDBC command the
// JSON literal sweep sends, one line of JSON with no spaces. The factor is
// spliced in as written, since a JSON encoder would write the number as 1.
func literalLengthCommand(digits int) string {
	return `{"type":"command","command":"parseDBC","dbc":{"version":"","messages":[{"id":200,` +
		`"name":"Msg","dlc":8,"sender":"ECU","senders":[],"extended":false,"signals":[{` +
		`"name":"Sel","startBit":0,"length":8,"byteOrder":"little_endian","signed":false,` +
		`"factor":1.` + strings.Repeat("0", digits) +
		`,"offset":0,"minimum":0,"maximum":255,"unit":"","presence":"always",` +
		`"receivers":["ECU"],"valueDescriptions":[]}]}],"signalGroups":[],` +
		`"environmentVars":[],"valueTables":[],"nodes":[{"name":"ECU"}],"comments":[],` +
		`"attributes":[],"unresolvedValueDescs":[]}}`
}

func literalLengths(quick bool) []int {
	if quick {
		return []int{25000, 50000, 100000}
	}
	return []int{12500, 25000, 50000, 100000}
}

// loadSession is a fresh session holding one load. run is the load, the one
// call timed and counted; check, called after both, refuses an answer the
// kernel did not accept; close ends the session.
type loadSession struct {
	run   func() error
	check func() error
	close func()
}

// openLoad opens a load's fresh session on the backend.
type openLoad func(*aletheia.FFIBackend) (loadSession, error)

// clientLoad opens a fresh client for the load, whose refusal is the error the
// client answers.
func clientLoad(load func(*aletheia.Client) error) openLoad {
	return func(backend *aletheia.FFIBackend) (loadSession, error) {
		client, err := aletheia.NewClient(backend)
		if err != nil {
			return loadSession{}, err
		}
		return loadSession{
			run:   func() error { return load(client) },
			check: func() error { return nil },
			close: func() { _ = client.Close() },
		}, nil
	}
}

// commandLoad opens a fresh session on the backend and sends the command
// through its raw command path, the reply checked by commandAccepted.
func commandLoad(command string) openLoad {
	return func(backend *aletheia.FFIBackend) (loadSession, error) {
		state, err := backend.Init()
		if err != nil {
			return loadSession{}, err
		}
		var reply string
		return loadSession{
			run: func() error {
				var err error
				reply, err = backend.Process(state, command)
				return err
			},
			check: func() error { return commandAccepted(command, reply) },
			close: func() { backend.Close(state) },
		}, nil
	}
}

// commandAccepted answers nil when the reply is the kernel accepting the
// parseDBC command, and otherwise the refusal, named by the reply's status,
// code and message.
func commandAccepted(command, reply string) error {
	var answer struct {
		Status  string `json:"status"`
		Code    string `json:"code"`
		Message string `json:"message"`
	}
	if err := json.Unmarshal([]byte(reply), &answer); err != nil {
		return fmt.Errorf("process answered a %d-byte parseDBC command with a reply that does not decode: %w", len(command), err)
	}
	if answer.Status != "success" {
		return fmt.Errorf("process refused a %d-byte parseDBC command: %s: %s: %s", len(command), answer.Status, answer.Code, answer.Message)
	}
	return nil
}

// dbcSizeLoad, textLiteralLoad and jsonLiteralLoad are the loads the load
// sweeps time at a size, the definition, the text or the command built before
// the load is timed.
func dbcSizeLoad(messages int) openLoad {
	dbc := dbcSizeDBC(messages)
	return clientLoad(func(client *aletheia.Client) error {
		_, err := client.ParseDBC(ctx, dbc)
		return err
	})
}

func textLiteralLoad(digits int) openLoad {
	text := literalLengthText(digits)
	return clientLoad(func(client *aletheia.Client) error {
		_, err := client.ParseDBCText(ctx, text)
		return err
	})
}

func jsonLiteralLoad(digits int) openLoad {
	return commandLoad(literalLengthCommand(digits))
}

// allocatedBytes reads the kernel runtime's allocation count, which the
// backend the program opened has started.
func allocatedBytes() (uint64, error) {
	allocated, ok := aletheia.AllocatedBytes()
	if !ok {
		return 0, errors.New("the kernel's allocation count answered no count: the runtime has not started")
	}
	return allocated, nil
}

// loadCost is a load's seconds and the bytes the kernel's runtime allocated
// while it ran.
type loadCost struct {
	seconds        float64
	allocatedBytes uint64
}

// minLoad runs the load numRuns times, each in a fresh session closed after,
// and answers the least seconds and the least allocated bytes of its runs.
// Only the load is timed, and the allocation count is read on either side of
// the timed span, after the session is open: the session's start and the
// check of the reply are in neither number, and the collection each read
// runs is not in the seconds. The bytes are the kernel runtime's, everything
// it runs for the command, and not what the binding builds on the Go heap.
// The least, not the mean: the gate compares a sweep's last point with its
// first, and the least is the least noisy estimate of the work. A refused
// load ends the program, naming the load and the refusal.
func minLoad(backend *aletheia.FFIBackend, what string, numRuns int, open openLoad) loadCost {
	run := func() (loadCost, error) {
		session, err := open(backend)
		if err != nil {
			return loadCost{}, err
		}
		defer session.close()
		before, err := allocatedBytes()
		if err != nil {
			return loadCost{}, err
		}
		start := time.Now()
		if err := session.run(); err != nil {
			return loadCost{}, err
		}
		seconds := time.Since(start).Seconds()
		after, err := allocatedBytes()
		if err != nil {
			return loadCost{}, err
		}
		if err := session.check(); err != nil {
			return loadCost{}, err
		}
		return loadCost{seconds: seconds, allocatedBytes: after - before}, nil
	}
	seconds := make([]float64, 0, numRuns)
	allocated := make([]uint64, 0, numRuns)
	for r := 0; r < numRuns; r++ {
		cost, err := run()
		if err != nil {
			die("%s run %d/%d failed: %v", what, r+1, numRuns, err)
		}
		seconds = append(seconds, cost.seconds)
		allocated = append(allocated, cost.allocatedBytes)
	}
	return loadCost{seconds: slices.Min(seconds), allocatedBytes: slices.Min(allocated)}
}

// sweep measures a sweep's points in order. Every sweep takes its baseline
// from its own first row.
func sweep[V any](points int, at func(int) V) []V {
	values := make([]V, 0, points)
	for i := 0; i < points; i++ {
		values = append(values, at(i))
	}
	return values
}

// loadPoint is one row of a load sweep, rounded as the schema pins it: the
// size, the least seconds and allocated bytes, the rate in size units a
// second, and that rate over the first row's.
type loadPoint struct {
	size           int
	seconds        float64
	allocatedBytes uint64
	rate           float64
	relative       float64
}

// loadSweep runs one load at the warmup size, its cost discarded so that a
// once-per-process allocation does not land in the first point, then
// measures the load at each size, unit naming what a size counts.
func loadSweep(backend *aletheia.FFIBackend, numRuns int, unit string, warmup int, sizes []int, load func(int) openLoad) []loadPoint {
	_ = minLoad(backend, fmt.Sprintf("warmup load of %d %s", warmup, unit), 1, load(warmup))
	costs := sweep(len(sizes), func(i int) loadCost {
		return minLoad(backend, fmt.Sprintf("load of %d %s", sizes[i], unit), numRuns, load(sizes[i]))
	})
	points := make([]loadPoint, 0, len(sizes))
	for i, cost := range costs {
		rate := float64(sizes[i]) / cost.seconds
		points = append(points, loadPoint{
			size: sizes[i], seconds: round4(cost.seconds), allocatedBytes: cost.allocatedBytes, rate: round1(rate),
			relative: round3(relativeOf(rate, float64(sizes[0])/costs[0].seconds)),
		})
	}
	return points
}

// printLoadSweep prints a load sweep's table under its heading, the
// allocated bytes beside the time.
func printLoadSweep(out io.Writer, heading, sizeColumn, rateColumn, expected string, points []loadPoint) {
	fmt.Fprintf(out, "\n%s\n%s\n%s\n", strings.Repeat("=", 70), heading, strings.Repeat("=", 70))
	fmt.Fprintf(out, "%10s %10s %16s %14s %10s\n", sizeColumn, "Time (s)", "Allocated (B)", rateColumn, "Relative")
	fmt.Fprintf(out, "%s\n", strings.Repeat("-", 64))
	for _, p := range points {
		fmt.Fprintf(out, "%10d %10.4f %16d %14.1f %9.3fx\n", p.size, p.seconds, p.allocatedBytes, p.rate, p.relative)
	}
	fmt.Fprintf(out, "\nExpected: %s\n", expected)
}

func runScaling(backend *aletheia.FFIBackend, out io.Writer, numRuns int, quick bool) scalingResults {
	fams := families()
	can20, canfd := fams[0], fams[1]
	numFrames := 10000
	if quick {
		numFrames = 5000
	}

	fmt.Fprintf(out, "\n%s\nScaling (runs=%d, quick=%v)\n%s\n", strings.Repeat("=", 70), numRuns, quick, strings.Repeat("=", 70))

	// Warmup.
	_ = meanFPS(backend, can20, makeProperties(1), 1000, 1)

	scanTrace := func(f frameFamily, props []aletheia.Formula) []traceSizeRow {
		sizes := traceSizes(quick)
		values := sweep(len(sizes), func(i int) float64 {
			return meanFPS(backend, f, props, sizes[i], numRuns)
		})
		rows := make([]traceSizeRow, 0, len(sizes))
		for i, m := range values {
			rows = append(rows, traceSizeRow{Frames: sizes[i], FPS: round1(m), Relative: round3(relativeOf(m, values[0]))})
		}
		return rows
	}

	traceCAN20 := scanTrace(can20, []aletheia.Formula{alwaysBetween("EngineSpeed", 0, 8000)})
	traceCANFD := scanTrace(canfd, []aletheia.Formula{alwaysBetween("GPSSpeed", 0, 655)})

	counts := []int{1, 2, 3, 5, 7, 10}
	countValues := sweep(len(counts), func(i int) float64 {
		return meanFPS(backend, can20, makeProperties(counts[i]), numFrames, numRuns)
	})
	propCount := make([]propCountRow, 0, len(counts))
	for i, m := range countValues {
		propCount = append(propCount, propCountRow{
			Properties: counts[i], FPS: round1(m), USPerFrame: round1(usPerFrameOf(m)),
			Relative: round3(relativeOf(m, countValues[0])),
		})
	}

	levels := complexityLevels()
	levelValues := sweep(len(levels), func(i int) float64 {
		return meanFPS(backend, can20, levels[i].props, numFrames, numRuns)
	})
	complexity := make([]complexityRow, 0, len(levels))
	for i, m := range levelValues {
		complexity = append(complexity, complexityRow{
			Complexity: levels[i].label, FPS: round1(m), USPerFrame: round1(usPerFrameOf(m)),
			Relative: round3(relativeOf(m, levelValues[0])),
		})
	}

	dbcPoints := loadSweep(backend, numRuns, "messages", 500, dbcSizes(quick), dbcSizeLoad)
	dbcSize := make([]dbcSizeRow, 0, len(dbcPoints))
	for _, p := range dbcPoints {
		dbcSize = append(dbcSize, dbcSizeRow{
			Messages: p.size, Seconds: p.seconds, AllocatedBytes: p.allocatedBytes, MessagesPerSec: p.rate, Relative: p.relative,
		})
	}
	printLoadSweep(out, "5. DBC Size Scaling", "Messages", "Messages/sec",
		"the allocated bytes double with the messages (the check gates them; the time decides nothing)", dbcPoints)

	// The literal sweeps load one number of growing digits, through the DBC
	// text and through a parseDBC command.
	scanLiteral := func(heading, route string, load func(int) openLoad) []literalLengthRow {
		points := loadSweep(backend, numRuns, "digits in a "+route, 1000, literalLengths(quick), load)
		rows := make([]literalLengthRow, 0, len(points))
		for _, p := range points {
			rows = append(rows, literalLengthRow{
				Digits: p.size, Seconds: p.seconds, AllocatedBytes: p.allocatedBytes, DigitsPerSec: p.rate, Relative: p.relative,
			})
		}
		printLoadSweep(out, heading, "Digits", "Digits/sec",
			"the allocated bytes double with the digits (the check gates them; the time decides nothing)", points)
		return rows
	}
	textLiteralLength := scanLiteral("6. Text Literal Length Scaling", "DBC text", textLiteralLoad)
	jsonLiteralLength := scanLiteral("7. JSON Literal Length Scaling", "parseDBC command", jsonLiteralLoad)

	fmt.Fprintf(out, "%s\n", strings.Repeat("=", 70))
	return scalingResults{
		TraceSizeCAN20:     traceCAN20,
		TraceSizeCANFD:     traceCANFD,
		PropertyCount:      propCount,
		PropertyComplexity: complexity,
		DBCSize:            dbcSize,
		TextLiteralLength:  textLiteralLength,
		JSONLiteralLength:  jsonLiteralLength,
	}
}

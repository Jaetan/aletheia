// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

import (
	"fmt"
	"io"
	"slices"
	"strings"
	"time"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// Scaling reports five sweeps under one mapping. The field order below is the
// wire order benchmarks/SCHEMA.yaml pins across the four bindings.
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
	MessagesPerSec float64 `json:"messages_per_sec"`
	Relative       float64 `json:"relative"`
}

type scalingResults struct {
	TraceSizeCAN20     []traceSizeRow  `json:"trace_size_can20"`
	TraceSizeCANFD     []traceSizeRow  `json:"trace_size_canfd"`
	PropertyCount      []propCountRow  `json:"property_count"`
	PropertyComplexity []complexityRow `json:"property_complexity"`
	DBCSize            []dbcSizeRow    `json:"dbc_size"`
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

// minLoadSeconds loads the definition numRuns times, each on a fresh client
// closed after, and answers the fastest load in seconds. Only ParseDBC is
// timed. The minimum, not the mean: the sweep compares two sizes' times, and
// the fastest load is the least noisy estimate of the work.
func minLoadSeconds(backend *aletheia.FFIBackend, dbc aletheia.DBCDefinition, numRuns int) float64 {
	load := func() (float64, error) {
		client, err := aletheia.NewClient(backend)
		if err != nil {
			return 0, err
		}
		defer client.Close()
		start := time.Now()
		if _, err := client.ParseDBC(ctx, dbc); err != nil {
			return 0, err
		}
		return time.Since(start).Seconds(), nil
	}
	times := make([]float64, 0, numRuns)
	for r := 0; r < numRuns; r++ {
		secs, err := load()
		if err != nil {
			die("dbc size point (%d messages) run %d/%d failed: %v", len(dbc.Messages), r+1, numRuns, err)
		}
		times = append(times, secs)
	}
	return slices.Min(times)
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

	// Every sweep takes its baseline from its own first row.
	sweep := func(points int, at func(int) float64) []float64 {
		values := make([]float64, 0, points)
		for i := 0; i < points; i++ {
			values = append(values, at(i))
		}
		return values
	}

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

	// Warmup.
	_ = minLoadSeconds(backend, dbcSizeDBC(500), 1)

	// The definition is built outside the timed load.
	dbcCounts := dbcSizes(quick)
	loadTimes := sweep(len(dbcCounts), func(i int) float64 {
		return minLoadSeconds(backend, dbcSizeDBC(dbcCounts[i]), numRuns)
	})
	dbcSize := make([]dbcSizeRow, 0, len(dbcCounts))
	for i, secs := range loadTimes {
		mps := float64(dbcCounts[i]) / secs
		dbcSize = append(dbcSize, dbcSizeRow{
			Messages: dbcCounts[i], Seconds: round4(secs), MessagesPerSec: round1(mps),
			Relative: round3(relativeOf(mps, float64(dbcCounts[0])/loadTimes[0])),
		})
	}

	fmt.Fprintf(out, "\n%s\n5. DBC Size Scaling\n%s\n", strings.Repeat("=", 70), strings.Repeat("=", 70))
	fmt.Fprintf(out, "%10s %10s %14s %10s\n", "Messages", "Time (s)", "Messages/sec", "Relative")
	fmt.Fprintf(out, "%s\n", strings.Repeat("-", 47))
	for _, r := range dbcSize {
		fmt.Fprintf(out, "%10d %10.4f %14.1f %9.3fx\n", r.Messages, r.Seconds, r.MessagesPerSec, r.Relative)
	}
	fmt.Fprintf(out, "\nExpected: Relative stays near 1.0x (load time linear in the number of messages)\n")

	fmt.Fprintf(out, "%s\n", strings.Repeat("=", 70))
	return scalingResults{
		TraceSizeCAN20:     traceCAN20,
		TraceSizeCANFD:     traceCANFD,
		PropertyCount:      propCount,
		PropertyComplexity: complexity,
		DBCSize:            dbcSize,
	}
}

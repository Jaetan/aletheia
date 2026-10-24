//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The package's examples, which godoc shows beside what they illustrate and go
// test runs, each checked against its Output. Each opens the library
// ALETHEIA_LIB names, as a reader's program does; TestMain sets the variable to
// the library the tests find when the environment leaves it unset.
package aletheia_test

import (
	"context"
	"errors"
	"fmt"
	"io"
	"log"
	"log/slog"
	"slices"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// One message, one 16-bit speed signal at a tenth of a km/h per bit.
const exampleDBC = `VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 256 Engine: 8 ECU
 SG_ Speed : 0|16@1+ (0.1,0) [0|6553.5] "km/h" ECU
`

func Example() {
	backend, err := aletheia.NewFFIBackendFromEnv()
	if err != nil {
		log.Fatal(err)
	}
	client, err := aletheia.NewClient(backend)
	if err != nil {
		log.Fatal(err)
	}
	defer client.Close()

	ctx := context.Background()
	parsed, err := client.ParseDBCText(ctx, exampleDBC)
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println(len(parsed.Warnings), "validation warning(s)")

	id, _ := aletheia.NewStandardID(0x100)
	dlc, _ := aletheia.NewDLC(8)
	result, err := client.ExtractSignals(ctx, id, dlc, aletheia.FramePayload{0xA0, 0x0F, 0, 0, 0, 0, 0, 0})
	if err != nil {
		log.Fatal(err)
	}
	speed, _ := result.Get("Speed")
	fmt.Printf("Speed = %d/%d km/h\n", speed.Numerator, speed.Denominator)
	// Output:
	// 0 validation warning(s)
	// Speed = 400/1 km/h
}

func Example_options() {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	backend, err := aletheia.NewFFIBackendFromEnv(
		aletheia.WithRTSCores(1),
		aletheia.WithFFILogger(logger),
	)
	if err != nil {
		log.Fatal(err)
	}
	speedLimit := aletheia.CheckSignal("Speed").NeverExceeds(aletheia.IntRational(220))
	client, err := aletheia.NewClient(
		backend,
		aletheia.WithLogger(logger),
		aletheia.WithDefaultChecks(speedLimit),
	)
	if err != nil {
		log.Fatal(err)
	}
	defer client.Close()

	ctx := context.Background()
	if _, err := client.ParseDBCText(ctx, exampleDBC); err != nil {
		log.Fatal(err)
	}
	// AddChecks sets the default checks, then any it is given, as the properties.
	if err := client.AddChecks(ctx, nil); err != nil {
		log.Fatal(err)
	}
	if err := client.StartStream(ctx); err != nil {
		log.Fatal(err)
	}
	id, _ := aletheia.NewStandardID(0x100)
	dlc, _ := aletheia.NewDLC(8)
	// Raw 0x0FA0 decodes to 400 km/h, which the default check refuses.
	resp, err := client.SendFrame(ctx, aletheia.Timestamp{Microseconds: 1000}, id, dlc,
		aletheia.FramePayload{0xA0, 0x0F, 0, 0, 0, 0, 0, 0}, nil, nil)
	if err != nil {
		log.Fatal(err)
	}
	if batch, ok := resp.(aletheia.PropertyBatch); ok {
		if v := batch.FirstViolation(); v != nil {
			fmt.Println("violation:", v.Reason)
		}
	}
	// Output:
	// violation: Atomic: predicate failed
}

func ExampleInputBoundExceededError() {
	backend, err := aletheia.NewFFIBackendFromEnv()
	if err != nil {
		log.Fatal(err)
	}
	client, err := aletheia.NewClient(backend)
	if err != nil {
		log.Fatal(err)
	}
	defer client.Close()

	// A factor past 2^63-1, which every number in a DBC is held to.
	const text = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 M: 8 ECU\n" +
		" SG_ S : 0|8@1+ (9223372036854775808,0) [0|255] \"\" ECU\n"
	_, err = client.ParseDBCText(context.Background(), text)
	var bex *aletheia.InputBoundExceededError
	if errors.As(err, &bex) {
		fmt.Printf("rejected %s = %d (limit %d)\n", bex.Field, bex.Observed, bex.Limit)
	}
	// Output:
	// rejected signal factor = 9223372036854775808 (limit 9223372036854775807)
}

func ExampleValidationFailedError() {
	backend, err := aletheia.NewFFIBackendFromEnv()
	if err != nil {
		log.Fatal(err)
	}
	client, err := aletheia.NewClient(backend)
	if err != nil {
		log.Fatal(err)
	}
	defer client.Close()

	// Eight unsigned bits carry 0 to 255, so a declared maximum of 1000 is refused.
	const text = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 M: 8 ECU\n" +
		" SG_ S : 0|8@1+ (1,0) [0|1000] \"\" ECU\n"
	_, err = client.ParseDBCText(context.Background(), text)
	var vfe *aletheia.ValidationFailedError
	if errors.As(err, &vfe) {
		for _, issue := range vfe.Issues {
			fmt.Printf("[%s] %s: %s\n", issue.Severity, issue.Code, issue.Detail)
		}
	}
	// Output:
	// [error] range_exceeds_bits: Message 'M', signal 'S': declared maximum lies above the values its bits carry
}

func ExampleTextRoundTripFailedError() {
	backend, err := aletheia.NewFFIBackendFromEnv()
	if err != nil {
		log.Fatal(err)
	}
	client, err := aletheia.NewClient(backend)
	if err != nil {
		log.Fatal(err)
	}
	defer client.Close()

	ctx := context.Background()
	// Payload is multiplexed on Mux; text names one selector value per signal.
	const text = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 M: 8 ECU\n" +
		" SG_ Mux M : 0|8@1+ (1,0) [0|255] \"\" ECU\n" +
		" SG_ Payload m1 : 8|8@1+ (1,0) [0|255] \"\" ECU\n"
	parsed, err := client.ParseDBCText(ctx, text)
	if err != nil {
		log.Fatal(err)
	}
	dbc := parsed.DBC
	dbc.Messages[0].Signals[1].Presence = aletheia.Multiplexed{
		Multiplexor: "Mux", MultiplexValues: []aletheia.MultiplexValue{1, 2},
	}
	_, err = client.FormatDBCText(ctx, dbc)
	var trte *aletheia.TextRoundTripFailedError
	if errors.As(err, &trte) {
		for _, issue := range trte.Issues {
			fmt.Printf("[%s] %s\n", issue.Severity, issue.Code)
		}
	}
	// Output:
	// [error] text_roundtrip_divergence
	// [warning] multi_value_mux_selector
}

func ExampleSignal() {
	backend, err := aletheia.NewFFIBackendFromEnv()
	if err != nil {
		log.Fatal(err)
	}
	client, err := aletheia.NewClient(backend)
	if err != nil {
		log.Fatal(err)
	}
	defer client.Close()

	ctx := context.Background()
	if _, err := client.ParseDBCText(ctx, exampleDBC); err != nil {
		log.Fatal(err)
	}
	atMost220 := aletheia.Signal("Speed").LessThanOrEqual(aletheia.IntRational(220))
	property := aletheia.Always{Inner: aletheia.Atomic{Predicate: atMost220}}
	if err := client.SetProperties(ctx, []aletheia.Formula{property}); err != nil {
		log.Fatal(err)
	}
	if err := client.StartStream(ctx); err != nil {
		log.Fatal(err)
	}
	id, _ := aletheia.NewStandardID(0x100)
	dlc, _ := aletheia.NewDLC(8)
	resp, err := client.SendFrame(ctx, aletheia.Timestamp{Microseconds: 1000}, id, dlc,
		aletheia.FramePayload{0xA0, 0x0F, 0, 0, 0, 0, 0, 0}, nil, nil) // 400 km/h
	if err != nil {
		log.Fatal(err)
	}
	if batch, ok := resp.(aletheia.PropertyBatch); ok && batch.FirstViolation() != nil {
		fmt.Println("violation:", batch.FirstViolation().Reason)
	}
	// Output:
	// violation: Atomic: predicate failed
}

func ExampleClient_SendFramesSeq() {
	backend, err := aletheia.NewFFIBackendFromEnv()
	if err != nil {
		log.Fatal(err)
	}
	client, err := aletheia.NewClient(backend)
	if err != nil {
		log.Fatal(err)
	}
	defer client.Close()

	ctx := context.Background()
	if _, err := client.ParseDBCText(ctx, exampleDBC); err != nil {
		log.Fatal(err)
	}
	speedLimit := aletheia.Always{Inner: aletheia.Atomic{
		Predicate: aletheia.Signal("Speed").LessThanOrEqual(aletheia.IntRational(220)),
	}}
	if err := client.SetProperties(ctx, []aletheia.Formula{speedLimit}); err != nil {
		log.Fatal(err)
	}
	if err := client.StartStream(ctx); err != nil {
		log.Fatal(err)
	}
	id, _ := aletheia.NewStandardID(0x100)
	dlc, _ := aletheia.NewDLC(8)
	frames := []aletheia.Frame{
		{Timestamp: aletheia.Timestamp{Microseconds: 1000}, ID: id, DLC: dlc,
			Data: aletheia.FramePayload{0xE8, 0x03, 0, 0, 0, 0, 0, 0}}, // 100 km/h
		{Timestamp: aletheia.Timestamp{Microseconds: 2000}, ID: id, DLC: dlc,
			Data: aletheia.FramePayload{0xA0, 0x0F, 0, 0, 0, 0, 0, 0}}, // 400 km/h
	}
	for resp, err := range client.SendFramesSeq(ctx, slices.Values(frames)) {
		if err != nil {
			log.Fatal(err) // iteration has stopped
		}
		if batch, ok := resp.(aletheia.PropertyBatch); ok && batch.FirstViolation() != nil {
			fmt.Println("violation:", batch.FirstViolation().Reason)
		} else {
			fmt.Println("no verdict yet")
		}
	}
	// Output:
	// no verdict yet
	// violation: Atomic: predicate failed
}

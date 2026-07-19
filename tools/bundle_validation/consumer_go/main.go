// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Bundle-consumer fixture (Go): drives the shared release-bundle scenario
// through the bundled module — env-constructor (the ALETHEIA_LIB seam set by
// the bundle's env.sh), ParseDBCText of a real .dbc, an
// Always(VehicleSpeed < 100) LTL property, one conforming and one violating
// frame, exactly one violation on the expected property, EndStream.  Wired to
// the bundle by tools/bundle_validate.py, which executes the
// "go mod edit -replace" + "go get" lines printed by the bundle's install.sh
// verbatim.
package main

import (
	"context"
	"fmt"
	"os"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

func run() error {
	if len(os.Args) != 2 {
		return fmt.Errorf("usage: %s <scenario-dbc-path>", os.Args[0])
	}
	text, err := os.ReadFile(os.Args[1])
	if err != nil {
		return err
	}

	// Env-constructor: resolves the shared library through ALETHEIA_LIB.
	backend, err := aletheia.NewFFIBackendFromEnv()
	if err != nil {
		return fmt.Errorf("NewFFIBackendFromEnv: %w", err)
	}
	client, err := aletheia.NewClient(backend)
	if err != nil {
		return fmt.Errorf("NewClient: %w", err)
	}
	defer func() { _ = client.Close() }()

	ctx := context.Background()
	parsed, err := client.ParseDBCText(ctx, string(text))
	if err != nil {
		return fmt.Errorf("ParseDBCText: %w", err)
	}
	if len(parsed.DBC.Messages) != 2 {
		return fmt.Errorf("vehicle.dbc should carry the VehicleDynamics + BrakeStatus messages, got %d messages", len(parsed.DBC.Messages))
	}

	// Always(VehicleSpeed < 100 kph).
	prop := aletheia.Always{Inner: aletheia.Atomic{
		Predicate: aletheia.Signal("VehicleSpeed").LessThan(aletheia.IntRational(100)),
	}}
	if err := client.SetProperties(ctx, []aletheia.Formula{prop}); err != nil {
		return fmt.Errorf("SetProperties: %w", err)
	}
	if err := client.StartStream(ctx); err != nil {
		return fmt.Errorf("StartStream: %w", err)
	}

	id, err := aletheia.NewStandardID(256)
	if err != nil {
		return err
	}
	dlc, err := aletheia.NewDLC(8)
	if err != nil {
		return err
	}

	// Conforming frame: VehicleSpeed raw 0x1388 (5000) -> 50.00 kph (factor 0.01).
	conforming := aletheia.FramePayload{0x88, 0x13, 0, 0, 0, 0, 0, 0}
	resp, err := client.SendFrame(ctx, aletheia.Timestamp{Microseconds: 1000}, id, dlc, conforming, nil, nil)
	if err != nil {
		return fmt.Errorf("SendFrame (conforming): %w", err)
	}
	if _, ok := resp.(aletheia.Ack); !ok {
		return fmt.Errorf("the conforming frame should be acknowledged without property events, got %T", resp)
	}

	// Violating frame: VehicleSpeed raw 0x4E20 (20000) -> 200.00 kph, over the bound.
	violating := aletheia.FramePayload{0x20, 0x4E, 0, 0, 0, 0, 0, 0}
	resp, err = client.SendFrame(ctx, aletheia.Timestamp{Microseconds: 2000}, id, dlc, violating, nil, nil)
	if err != nil {
		return fmt.Errorf("SendFrame (violating): %w", err)
	}
	batch, ok := resp.(aletheia.PropertyBatch)
	if !ok {
		return fmt.Errorf("the violating frame should produce a property batch, got %T", resp)
	}
	violations := 0
	for _, r := range batch.Results {
		if r.Verdict == aletheia.Fails {
			violations++
		}
	}
	if violations != 1 {
		return fmt.Errorf("expected exactly one violation from the violating frame, got %d", violations)
	}
	violation := batch.FirstViolation()
	if violation.PropertyIndex != 0 {
		return fmt.Errorf("the violation should name the single installed property, got index %d", violation.PropertyIndex)
	}
	if violation.Enrichment == nil {
		return fmt.Errorf("the violation should carry an enrichment")
	}
	if _, ok := violation.Enrichment.Signals["VehicleSpeed"]; !ok {
		return fmt.Errorf("the enrichment should carry the VehicleSpeed value")
	}

	if _, err := client.EndStream(ctx); err != nil {
		return fmt.Errorf("EndStream: %w", err)
	}

	fmt.Println("BUNDLE-CONSUMER go: OK — exactly one violation on the expected property")
	return nil
}

func main() {
	if err := run(); err != nil {
		fmt.Fprintf(os.Stderr, "BUNDLE-CONSUMER go: FAIL — %v\n", err)
		os.Exit(1)
	}
}

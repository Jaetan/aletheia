package aletheia_test

import (
	"errors"
	"strings"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// requireErrorContains asserts err is a non-nil *aletheia.Error whose message
// contains substr. Uses errors.As for proper unwrapping (G-6 review finding).
func requireErrorContains(t *testing.T, err error, substr string) {
	t.Helper()
	if err == nil {
		t.Fatal("expected error, got nil")
	}
	var e *aletheia.Error
	if !errors.As(err, &e) {
		t.Fatalf("expected *aletheia.Error, got %T: %v", err, err)
	}
	if !strings.Contains(err.Error(), substr) {
		t.Errorf("expected error containing %q, got: %v", substr, err)
	}
}

// dlc8 creates a DLC with value 8 for convenience in tests.
func dlc8() aletheia.DLC {
	d, _ := aletheia.NewDLC(8)
	return d
}

// testDBC returns a minimal DBC definition for testing.
func testDBC() aletheia.DbcDefinition {
	sid, _ := aletheia.NewStandardID(0x123)
	dlc, _ := aletheia.NewDLC(8)
	return aletheia.DbcDefinition{
		Version: "1.0",
		Messages: []aletheia.DbcMessage{
			{
				ID:     sid,
				Name:   "EngineData",
				DLC:    dlc,
				Sender: "ECU",
				Signals: []aletheia.DbcSignal{
					{
						Name:      "Speed",
						StartBit:  0,
						BitLength: 16,
						ByteOrder: aletheia.LittleEndian,
						IsSigned:  false,
						Factor:    aletheia.Rational{Numerator: 1, Denominator: 10},
						Offset:    aletheia.Rational{Numerator: 0, Denominator: 1},
						Minimum:   aletheia.Rational{Numerator: 0, Denominator: 1},
						Maximum:   aletheia.Rational{Numerator: 300, Denominator: 1},
						Unit:      "km/h",
						Presence:  aletheia.AlwaysPresent{},
					},
				},
			},
		},
	}
}

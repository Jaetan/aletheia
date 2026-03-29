package aletheia_test

import "github.com/aletheia-automotive/aletheia-go/aletheia"

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
						Factor:    0.1,
						Offset:    0,
						Minimum:   0,
						Maximum:   300,
						Unit:      "km/h",
						Presence:  aletheia.AlwaysPresent{},
					},
				},
			},
		},
	}
}

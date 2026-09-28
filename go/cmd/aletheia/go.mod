// The Aletheia command line, a module of its own because its template command
// writes the workbook through the Excel module, and the core module stays free
// of excelize: a consumer of the core binding depends on neither this module
// nor the Excel one.
//
// The core module is required at the version of the last release and the Excel
// module at v0.0.0, which no release carries; ../../go.work resolves both to
// this tree. The command is built from the workspace and is not in the bundle a
// release builds. This file carries no replace of its own: it would travel with
// the module.
module github.com/Jaetan/aletheia/go/cmd/aletheia

go 1.24.0

toolchain go1.24.6

require (
	github.com/Jaetan/aletheia/go/excel v0.0.0
	github.com/Jaetan/aletheia/go/v5 v5.0.0
)

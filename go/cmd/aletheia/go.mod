// The Aletheia command line, a module of its own because its template command
// writes the workbook through the Excel module, and the core module stays free
// of excelize: a consumer of the core binding depends on neither this module
// nor the Excel one.
//
// The core and Excel modules are required below at pseudo-versions of commits
// on main, which GitHub serves, so a tool resolving this module outside the
// workspace resolves it; ../../go.work resolves both to this tree during
// development. The command is not in the bundle a release builds. This file
// carries no replace of its own: it would travel with the module.
module github.com/Jaetan/aletheia/go/cmd/aletheia

go 1.26.0

require (
	github.com/Jaetan/aletheia/go/excel v0.0.0-20261120222537-2b12b86d9f6a
	github.com/Jaetan/aletheia/go/v5 v5.0.0-20261120132838-2150dabcfa97
)

require (
	github.com/richardlehane/mscfb v1.0.9 // indirect
	github.com/richardlehane/msoleps v1.0.6 // indirect
	github.com/tiendc/go-deepcopy v1.7.2 // indirect
	github.com/xuri/efp v0.0.3-0.20260924042702-217b81952dec // indirect
	github.com/xuri/excelize/v2 v2.11.1 // indirect
	github.com/xuri/nfp v0.0.2-0.20250530014748-2ddeb826f9a9 // indirect
	golang.org/x/crypto v0.58.0 // indirect
	golang.org/x/net v0.62.0 // indirect
	golang.org/x/text v0.43.0 // indirect
	gopkg.in/yaml.v3 v3.0.1 // indirect
)

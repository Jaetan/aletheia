// The Aletheia Excel loader, a module of its own so that excelize, and the
// cryptography, network and text packages it brings with it, are optional: a
// consumer driving checks from YAML or from code depends on the core module
// alone, and one wanting the workbook loaders adds this on top.
//
// The core module is required below at the placeholder version v0.0.0, which
// ../go.work resolves during development. This file carries no replace of its
// own: it would travel with the module.
module github.com/aletheia-automotive/aletheia-go/excel

go 1.24.0

toolchain go1.24.6

require (
	github.com/aletheia-automotive/aletheia-go v0.0.0
	github.com/xuri/excelize/v2 v2.10.1
)

require (
	github.com/richardlehane/mscfb v1.0.6 // indirect
	github.com/richardlehane/msoleps v1.0.6 // indirect
	github.com/tiendc/go-deepcopy v1.7.2 // indirect
	github.com/xuri/efp v0.0.1 // indirect
	github.com/xuri/nfp v0.0.2-0.20250530014748-2ddeb826f9a9 // indirect
	golang.org/x/crypto v0.48.0 // indirect
	golang.org/x/net v0.50.0 // indirect
	golang.org/x/text v0.34.0 // indirect
	gopkg.in/yaml.v3 v3.0.1 // indirect
)

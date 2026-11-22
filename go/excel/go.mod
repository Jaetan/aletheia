// The Aletheia Excel loader, a module of its own so that excelize, and the
// cryptography, network and text packages it brings with it, are optional: a
// consumer driving checks from YAML or from code depends on the core module
// alone, and one wanting the workbook loaders adds this on top.
//
// The core module is required below at the pseudo-version of a commit on main,
// which GitHub serves, so a tool resolving this module outside the workspace
// resolves it; ../go.work resolves it to this tree during development. Its path
// carries the matching major-version suffix, without which Go refuses any major
// above the first. This file carries no replace of its own: it would travel
// with the module.
module github.com/Jaetan/aletheia/go/excel

go 1.26.0

require (
	github.com/Jaetan/aletheia/go/v5 v5.0.0-20261120132838-2150dabcfa97
	github.com/xuri/excelize/v2 v2.11.1
	gopkg.in/yaml.v3 v3.0.1
)

require (
	github.com/richardlehane/mscfb v1.0.9 // indirect
	github.com/richardlehane/msoleps v1.0.6 // indirect
	github.com/tiendc/go-deepcopy v1.7.2 // indirect
	github.com/xuri/efp v0.0.3-0.20260924042702-217b81952dec // indirect
	github.com/xuri/nfp v0.0.2-0.20250530014748-2ddeb826f9a9 // indirect
	golang.org/x/crypto v0.58.0 // indirect
	golang.org/x/net v0.62.0 // indirect
	golang.org/x/text v0.43.0 // indirect
)

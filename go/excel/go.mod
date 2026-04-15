// Aletheia Excel loader — separate module so the heavy excelize dependency
// (and its transitive crypto / net / text chain) is fully optional. Users who
// want YAML- or code-driven checks can depend on aletheia-go alone; those
// who want the Excel template workflow add this module on top.
//
// The replace directive below pins this to the in-tree aletheia-go module so
// local development does not require a tagged release. Downstream consumers
// of a published version should drop the replace directive.
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

replace github.com/aletheia-automotive/aletheia-go => ../

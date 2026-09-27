module example.com/goosebugs

go 1.26

// goose and proofgen are built from this pinned upstream perennial
// (mit-pdos/perennial master, 2026-09-01), which has all the bugs.
tool (
	github.com/mit-pdos/perennial/goose/cmd/goose
	github.com/mit-pdos/perennial/goose/cmd/proofgen
)

require (
	github.com/fatih/color v1.19.0 // indirect
	github.com/mattn/go-colorable v0.1.14 // indirect
	github.com/mattn/go-isatty v0.0.20 // indirect
	github.com/mit-pdos/perennial v0.0.0-20260901084625-3fe5d0a957a9 // indirect
	github.com/pelletier/go-toml/v2 v2.4.3 // indirect
	github.com/pkg/errors v0.9.1 // indirect
	golang.org/x/mod v0.39.0 // indirect
	golang.org/x/sync v0.22.0 // indirect
	golang.org/x/sys v0.47.0 // indirect
	golang.org/x/tools v0.49.0 // indirect
)

# Agent Instructions

After every completed task, include a `Timing` section with:

- Total tool time.
- A breakdown of tool time by command or tool category, such as `make`, `go test`, `rg`/file reads, `apply_patch`, and other shell commands.
- Interrupted commands listed separately, without counting them as completed verification.

Use `/usr/bin/time -p` for long-running verification commands when practical.

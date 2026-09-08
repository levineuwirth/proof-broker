# Pinned checking libraries

Files are copied unchanged from the revisions in `sources.lock.json`, with
their upstream Apache-2.0 licenses. `run.py` checks every source hash before
building offline. Only the library modules and executable source actually used
are vendored; build configuration is generated in `.cache/`.

The exporter is built with Lean 4.32.0 to read the original task environment.
Its parser and Comparator's libraries are built with patched Lean 4.32.2.
Comparator's original project pins 4.34.0-rc2; the vendored comparison libraries
compile unchanged on 4.32.2. The project-owned replay adapter documents the
API adjustment and extra target checks in `../validate/Replay.lean`.

The NDJSON parser/replay boundary is used instead of importing a candidate
`.olean` into the final validator. We do not use Comparator's Landrun-based
CLI or its development fake-sandbox script; `../run.py` supplies the isolated
build/export/replay processes with Bubblewrap.

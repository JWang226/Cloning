# Build and verification commands

Run these commands from `formalization/`. The helpers use Python 3.9 or newer;
the fresh audit requires a POSIX environment (Linux, macOS, or WSL) and elan/Lake.

```sh
lake exe cache get
lake build All
python3 scripts/check_checkpoint.py
```

`lake build All` checks the current proof modules and the presentation entry points
with the pinned Lean toolchain. It is the portable replacement for the archived
`check_local.py`, whose defaults refer to the original author's machine.

`check_checkpoint.py` runs **no Lean process** and changes no repository files.
It verifies every original bundle checksum, the exact current `Cloning.lean` and
`Cloning/` source inventory, the dependency pins, all saved build-phase and audit
fingerprints, and the successful completion records. Original files moved during
reorganization are resolved in `verification/seventh-pass/` first, then at the
project root. The active proof sources are checked separately to prevent an
archived copy from masking changes.

The checker copies the audit evidence into temporary storage and runs the original
auditor's Python-only `--resummarize` mode. This independently rechecks the complete
module/export inventories in all three shards, identical repeated exports,
per-constant axiom reports, and all reported counts. The result must equal the
original completion summary. The extended `verification.json` must preserve every
field of `AUDIT-seventh-verification.json`.

This is a check of the saved certificate's integrity and agreement with the
sources, not a new kernel run or a cryptographic signature. It does not require or
compare local compiled artifacts against the original machine's `.olean` hashes.
The new import/`#check` entry points and `All.lean` are checked by Lake; the historical
all-constant audit covers the unchanged `Cloning` modules.

For a fresh kernel axiom audit:

```sh
python3 scripts/audit.py --jobs 3
# Or choose a new output directory:
python3 scripts/audit.py --jobs 3 --output /tmp/cloning-fresh-audit
```

The wrapper first runs `lake build All`, then uses `lake env` to run the **unchanged
historical audit engine** against the built Lake artifacts. Each worker imports
the full `Cloning` environment and audits disjoint module indices with Lean's
standard `collectAxioms`. The serial `Audit.lean` remains available for independent
reproduction. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.

The audit runs in temporary storage. Its proof-source snapshot, engine, generated
drivers, raw output, summary, build/audit logs, and `run.json` are retained in a new
`verification/runs/<UTC timestamp>/` directory, or the supplied `--output` directory.
The wrapper rejects existing destinations and destinations inside the seventh-pass
archive. No compiled artifacts are copied into the evidence. Source/configuration
and compiled project artifact hashes must remain unchanged throughout the audit.
Dependency binaries come from the pinned Lake installation; do not modify the
toolchain or package caches while the audit is running.

To inspect source scanning and driver generation without building or invoking Lean:

```sh
python3 scripts/audit.py --prepare-only --jobs 3 --output /tmp/cloning-audit-preview
```

This produces a snapshot explicitly marked `prepared_only`, not a passing audit.
For the saved serial driver, independent reproduction after a build is:

```sh
lake env lean -DautoImplicit=false verification/seventh-pass/Audit.lean
```

The historical archive is intentionally unchanged. Do not run its `audit.py`
directly in that directory: it expects the former layout and writes audit files.

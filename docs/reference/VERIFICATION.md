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
When `verification/latest.json` exists, it verifies the referenced completed full
build and axiom audit: every saved evidence hash, the exact current proof and
entry-point source inventory, dependency pins, successful return codes, and
source/artifact stability gates. It then replays the pinned audit engine's
Python-only `--resummarize` mode in temporary storage and requires an identical
summary, including complete export coverage and every axiom report. Both serial
and multi-worker evidence are supported.

Without a latest pointer, the checker validates the historical seventh-pass
checkpoint against the corresponding exact source inventory. The original
checkpoint is preserved separately; new proofs are certified by the latest full
audit, not by that historical record.

This checks saved evidence integrity and agreement with the current sources.
It is not a fresh kernel run or a cryptographic signature. It does not require
local compiled artifacts to match another machine's `.olean` hashes. The full
build includes all public entry points; the axiom audit covers all declarations
exported by the implementation modules imported by `Cloning.lean`.

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
For the current checkpoint's serial driver, independent reproduction after a build is:

```sh
lake env lean -DautoImplicit=false verification/kernel-compatible-pass/Audit.lean
```

The historical archive is intentionally unchanged. Do not run its `audit.py`
directly in that directory: it expects the former layout and writes audit files.

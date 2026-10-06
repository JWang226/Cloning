# Build and verification commands

For the complete reproducer, run from the repository root:

```sh
bash scripts/verify.sh all
```

Use `bash scripts/verify.sh lean` for just the Lean build and complete axiom audit.
The wrapper prepares dependencies and writes fresh logs under `.verify-work/run-*`.
See the [root README](https://github.com/JWang226/Cloning#check-it-yourself) for prerequisites and the
individual Comparator and Nanoda commands.

The lower-level commands below run from `formalization/`. The helpers use Python 3.9 or newer;
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
python3 scripts/audit.py
# Or choose a new output directory:
python3 scripts/audit.py --output /tmp/cloning-fresh-audit
```

The wrapper first runs `lake build All`, then uses `lake env` to run
`shared_audit.py` against the built Lake artifacts. The shared engine enumerates
every compiled declaration exported by the imported `Cloning` modules, including
private and generated declarations. It applies Lean's `CollectAxioms.collect`
with one shared visited set across all unique roots, so common proof dependencies
are traversed once. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.

The new evidence records the complete module/declaration inventory and the
**aggregate axiom union**. It does not assign that union to each individual
declaration. Exact inventory coverage, successful native traversal, and the
allowed-axiom policy must all pass. Stage messages and elapsed-time heartbeats
show that the process is running even while Lean buffers its standard output.

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
python3 scripts/audit.py --prepare-only --output /tmp/cloning-audit-preview
```

This produces a snapshot explicitly marked `prepared_only`, not a passing audit.
The new snapshot's `audit.py --resummarize` command validates and reconstructs
its saved summary without running Lean. It requires completed execution evidence;
driver generation alone cannot pass. `check_checkpoint.py` continues to validate
the published checkpoint selected by `verification/latest.json`.

For the original per-declaration axiom reports, select the archived engine:

```sh
python3 scripts/audit.py --engine historical --jobs 3
```

`--jobs` applies to the historical engine; the shared engine uses one process.
The root wrapper always selects the shared engine. The old `CLONING_AUDIT_JOBS`
setting no longer changes its worker count.

The historical engine repeats dependency traversal for each root and can take
over an hour. For the current checkpoint's serial driver, independent
reproduction after a build is:

```sh
lake env lean -DautoImplicit=false verification/kernel-compatible-pass/Audit.lean
```

The historical archive is intentionally unchanged. Do not run its `audit.py`
directly in that directory: it expects the former layout and writes audit files.

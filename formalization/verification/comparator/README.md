# Pinned statement comparison and kernel replay

From the repository root, run Comparator through the verification wrapper:

```bash
bash scripts/verify.sh comparator
# Build and audit Lean, then run Comparator and Nanoda in sequence:
bash scripts/verify.sh all
```

The other targets are `lean` for an `All` build and fresh full axiom audit, and
`nanoda` for the independent all-project-constant check. Each wrapper invocation
initializes the pinned dependency cache and saves its logs and fresh reports in
the root `.verify-work/run-*/` directory. The Comparator target builds `All`
before checking; `all` reuses the build from its Lean audit. It fetches and builds
the exact pinned checker tools without running `lake update`.
The Lean audit uses three workers by default; `CLONING_AUDIT_JOBS` selects a
different positive worker count for the `lean` and `all` targets.

**The root wrapper explicitly selects trusted local execution on macOS and
Linux. It does not sandbox build or exporter processes.** Statement comparison,
axiom checking, and Lean kernel replay still run, but this mode provides no
protection from malicious elaboration/native code or hostile `.olean` files.
Use the direct Linux sandboxed alternative below when that isolation is needed.

A successful full check requires Comparator's success marker and unchanged
audited sources, local compiled project artifacts, and pinned dependency
checkouts. Preparation and preflight commands are not proof-checking verdicts.
The wrapper's fresh Lean audit does not silently replace the audit selected by
the checker lock; source changes require a new passed full audit and an explicit
lock update.

The [current status](status.json) records a successful full
[Comparator run](records/20261004T055545.209379Z/run.json) bound to the
[kernel-compatible audit](../kernel-compatible-pass/run.json). All 27 explicit
statements and their proof dependencies passed statement comparison, axiom
checking, and Lean kernel replay using trusted local execution, no sandbox.
Earlier failed and passed attempts remain in the status history.

## Prerequisites and platforms

The root wrapper requires Python 3.10+, Bash, Git, curl, tar, elan/Lake with the
project's pinned **Lean 4.29.0-rc6**, a native C toolchain, and network access for
uncached pinned dependencies and tools. Comparator's wrapper target does not
require Go. The `nanoda` and `all` targets additionally require existing
Rustup/Cargo; the wrapper installs the pinned Rust 1.93.1 toolchain through
Rustup with the minimal profile.

## Direct runner and Linux sandbox

The direct runner retains Linux sandboxing as its default. From the repository
root, build the project with its existing toolchain and dependency lock, then
run the direct checks:

```bash
cd formalization
"$HOME/.elan/bin/lake" build All
LAKE="$HOME/.elan/bin/lake" bash verification/comparator/run.sh validate
LAKE="$HOME/.elan/bin/lake" bash verification/comparator/run.sh preflight
LAKE="$HOME/.elan/bin/lake" bash verification/comparator/run.sh
```

The sandboxed mode needs Linux, an unprivileged account, a kernel with Landlock
enabled, and the Go compiler recorded in `../tools-lock.json` (currently
`go1.25.0`). Go downloads
the dependencies fixed by upstream `go.mod`/`go.sum`; `-mod=readonly` prevents
dependency-file updates. The runner builds the pinned Landrun source and checks
that a write outside the allowed directory is denied. The upstream Comparator
uses Landrun's `--best-effort`; this is a filesystem sandbox check, not a claim
that every newer Landlock network/IPC feature is available.

macOS has no Linux Landlock. Use a Linux host/VM for the direct runner's default
mode. To select the root wrapper's trusted local mode directly, use these
commands from `formalization/`:

```bash
LAKE="$HOME/.elan/bin/lake" bash verification/comparator/run.sh preflight --trusted-local
LAKE="$HOME/.elan/bin/lake" bash verification/comparator/run.sh --trusted-local
```

This mode records `trusted-local-no-sandbox` and uses `trusted-landrun.py`.
The direct runner requires the explicit `--trusted-local` flag; the root
wrapper supplies it.

The direct full invocation prepares an isolated Lake wrapper and writes a fresh
`run.json` and `comparator.log` under `verification/comparator/.work/runs/` by
default. `--work /absolute/path` changes that directory;
`--lake /absolute/path/to/lake` or `LAKE` selects elan's Lake launcher. `setup`
builds tools only, and `prepare` creates the wrapper only. `CheckTypes.lean` is
an optional preparation diagnostic: after building the two wrapper modules,
`lake env lean --run CheckTypes.lean` in that wrapper compares their 27 explicit
types after removing source metadata. It does not inspect proof axioms or
perform kernel replay and is not a Comparator verdict.

## What is pinned and compared

`../tools-lock.json` fixes full commits for Comparator, lean4export,
Lean4Checker, Landrun, and Nanoda. Comparator and lean4export both have exact
`v4.29.0-rc6` upstream releases. No project toolchain change or copied 4.33-only
flag is used. Comparator's upstream manifest names an older exporter, so a
separate build copy receives a generated Lake configuration pointing at the
exact pinned exporter and checker checkouts. No upstream Lean code is patched.
Lean4Checker's own toolchain file is older; as an upstream dependency it is
compiled by Comparator's rc6 root toolchain, exactly as Lake normally does.

`Challenge.lean` and `Solution.lean` declare the same 27 names with explicit
mathematical statements. `claims.json` maps these to the manuscript labels and
actual implementation declarations. The challenge has deliberate `sorry`
proofs; these are specification holes, **outside the audited project library**,
and its proofs are not the candidate solution. The solution gives real proofs.
The challenge does not obtain its type by inspecting a target theorem or
defining a synonym for that theorem's inferred type.

The challenge uses this project's mathematical definitions. Their trusted
reference is the exact source/config inventory in the **hash-pinned passed
full audit selected by tools-lock.json**, not a fresh snapshot silently accepted at runtime.
Changes to those sources, project configuration, or pinned challenge files
cause rejection. Dependency source checkouts must match the immutable Lake
manifest and have no tracked changes. The wrapper reuses built `.olean` files;
their source/cache provenance is still trusted at the build boundary. A clean
rebuild on a separately trusted host gives stronger provenance than reusing an
existing local cache. Hashes alone do not show that a compiled file came from
its claimed source.

At the pinned [Comparator implementation](https://github.com/leanprover/comparator/blob/a4f696825c583ed8a5b4060d9a0faa5b882d365b/Main.lean),
the sequence is challenge build/export, solution build/export, exact statement
and transitive statement-constant comparison, solution proof dependency axiom
check, then reconstruction/replay in an empty Lean kernel environment. The
comparison walks definitions and their dependencies, so merely substituting a
different mathematical definition in the solution does not pass. The allowed
axioms are only `propext`, `Quot.sound`, and `Classical.choice`.

Comparator's scope is the selected 27 statements and their proof dependencies.
It does not automatically replay every unrelated declaration merely because a
module was imported. The [Nanoda reproducer](../nanoda/README.md) separately
targets **all 14,345 audited project constants and their dependencies** with an
independent Rust kernel. Neither check establishes that a human specification
faithfully describes the manuscript; the explicit statements and
`../../PROOF_MAP.md` remain the material for that review.

## Runtime and evidence

The current archived run records 348.8 seconds between its start and completion timestamps.
The archived [macOS `/usr/bin/time -l` report](records/20261004T055545.209379Z/resources.json) recorded 3,614,605,312 bytes (3.37 GiB) maximum resident set size for the timed runner command. This is not simultaneous aggregate memory across all processes.
These are observations of this run, not resource estimates for another machine or workload.
Export and replay can take substantial memory and time. This runner imposes no
guessed memory cap and does not silently omit declarations to finish sooner. Use an adequately
resourced machine and retain the complete new run directory, including failure
logs. Never replace the saved completion audit with a Comparator configuration
check.

The [compatibility report](../kernel-compatibility.md) explains the source annotations and the historical 14,375-constant inventory. These annotations changed no mathematical statement or proof body in the project library.

The [initial failed wrapper build](records/20261004T035736.789819Z/run.json) reached the 1,800,000-heartbeat cap while elaborating `lifted_kernel_bound`. Its [Solution.lean](Solution.lean) proof was repaired by performing the scalar-fidelity simplification once in a generic helper, then instantiating that helper. The target statements and the 1,800,000-heartbeat cap remained unchanged. The [first successful run](records/20261004T040413.949258Z/run.json) remains historical evidence bound to the original completion audit.

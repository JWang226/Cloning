# Independent Nanoda reproduction

From the repository root, run the independent checker through the verification
wrapper:

```bash
bash scripts/verify.sh nanoda
# Build and audit Lean, then run Comparator and Nanoda in sequence:
bash scripts/verify.sh all
```

The other targets are `lean` for an `All` build and fresh full axiom audit, and
`comparator` for comparison and Lean kernel replay of the 27 explicit statements.
Each invocation initializes the pinned dependency cache and saves its logs and
fresh reports in the root `.verify-work/run-*/` directory. The Nanoda target
installs Rust 1.93.1 through existing Rustup with the minimal profile, then runs
the pinned exporter and unmodified checker with one thread. It does not run
`lake update`.
The Lean audit uses one shared dependency traversal across every compiled project
declaration; the [audit guide](../../scripts/README.md) also documents the
historical per-declaration auditor.

The wrapper requires Python 3.10+, Bash, Git, curl, tar, a native C toolchain,
elan/Lake with the project's pinned Lean toolchain, and existing Rustup/Cargo.
Its first run needs network access for uncached pinned dependencies, tools, and
the Rust toolchain. It does not sandbox builds or exports. The Comparator
target used by `all` also explicitly runs without a sandbox; its direct Linux
sandboxed alternative is documented in the [Comparator README](../comparator/README.md).

The [current status](status.json) records a successful full [Nanoda run](records/20261004T055629.624926Z/run.json). The pinned, unmodified independent Rust kernel checked 83,433 exported declarations: all 14,345 project roots from the 982 implementation modules, including private and generated declarations, and all their transitive dependencies. The exact input is bound to the [kernel-compatible audit](../kernel-compatible-pass/run.json). The archived timestamps record 523.1 seconds end to end. The archived [macOS `/usr/bin/time -l` report](records/20261004T055629.624926Z/resources.json) recorded 3,268,395,008 bytes (3.04 GiB) maximum resident set size for the timed runner command. This is not simultaneous aggregate memory across all processes. Observed run measurements are not resource estimates for another machine or workload.

The [compatibility report](../kernel-compatibility.md) records 30 `noncomputable` prefixes in 15 files. They prevent generation of the 30 partial runtime helpers that caused the [first export-safety failure](records/20261004T040757.497668Z/run.json). The original completion audit covered 14,375 project constants. Every old safe project declaration is retained; the current full inventory supplies all roots, with no filtering and no exporter or kernel patch.

## Direct preflight and runner

The direct runner remains available on Linux and macOS. From the repository
root:

```sh
cd formalization
bash verification/nanoda/run.sh --preflight
python3 -B verification/nanoda/test_reproduce.py
```

Preflight reads the saved audit, validates its pinned SHA-256, verifies its source
hashes against the current project, recovers the complete module inventory, and
checks the axiom configuration. It does not access the network or execute Lean,
lean4export, Cargo, or Nanoda. Exit 2 means missing prerequisites, exit 1 means a
validation failure, and exit 0 means preflight is ready; none is a proof-checking
success. Preflight checks executable availability, not an installed Rust
toolchain or network connectivity.

To run the direct full check from `formalization/`, install the explicitly
pinned Rust toolchain first:

```sh
rustup toolchain install 1.93.1 --profile minimal
bash verification/nanoda/run.sh --run --threads 1
```

The direct runner requires Python 3.9+, Bash, Git, elan/Lake with the project's
pinned Lean toolchain, Rustup/Cargo, and native build tools. It discovers Lake in
`PATH` or `~/.elan/bin`; Rust tools are also searched
in `~/.cargo/bin`. The first full run needs network access for the two pinned Git
checkouts, locked Cargo dependencies, and any uncached Lean dependencies. It
does not install Rust automatically; the root wrapper performs that setup.
`--work /absolute/path` selects another
work directory. Full export and unmodified Nanoda checking can require substantial
memory, disk, and time. The archived measurements above describe one completed
run, not a resource or runtime estimate for a new run.

`--run` performs the following stages, recording a separate output directory and
`run.json` for every attempt under the selected work directory (by default,
`verification/nanoda/.work/run-*/`):

1. Bind the full declaration inventory to the current source files and the pinned
   successful audit in [`../tools-lock.json`](../tools-lock.json).
2. Check out the exact lean4export and Nanoda commits, reject modified tool source,
   build the exporter with the project's Lean version, and build unmodified Nanoda
   with `rustup run 1.93.1 cargo build --release --locked`.
3. Build `All`, hash the current compiled `Cloning` artifacts, then export the
   complete project root list and Nat/String/Quot prerequisites in one stream.
4. Verify export format/version, actual presence of every requested root, absence
   of unsafe/partial declarations, and the strict three-axiom policy. Run Nanoda
   against that exact export and require both exit zero and an unqualified
   `Checked <n> declarations with no errors` with the matching declaration count.
5. Recheck source binding, pinned dependency Git revisions and tracked-source
   cleanliness, tool source, harness, roots, checker configuration,
   checker binary, export, and compiled-artifact hashes before recording success.

The default thread count is one. A higher positive `--threads` value changes
Nanoda's parallelism, not the declaration scope or allowed axioms. A failed or
interrupted attempt never becomes a passed check. Logs and partial export files
are preserved. There is no reuse/skip-export option and no partial-root option.
The axiom report goes to stdout; the configuration guard requires stdout when
reporting is enabled, and a qualified success message remains a failure.

## Export scope and trust boundary

The normal upstream CLI is `lake env /path/to/lean4export Cloning`. That exports
public constants from the whole imported environment, including unused prelude
axioms, and omits internal names as independent roots. We instead select **all**
project declarations from the hash-bound full audit, including internal names,
then use the exporter's recursive dependency traversal. All actual dependencies
are retained. This avoids adding unused `sorryAx` or `Lean.trustCompiler` as roots.

[`ExportCloning.lean`](ExportCloning.lean) is a small file-based front end to the
unchanged pinned exporter API. It uses the same `importModules`, `initState`,
`dumpMetadata`, and `dumpConstant` calls as upstream `Main.lean`. Reading the roots
from a file avoids operating-system command-line length limits and repeated
exports of the same dependencies. It fails if a selected name cannot be parsed or
found. The current inventory uses ordinary ASCII Lean names; the Python front end
fails on a future inventory requiring a new name-escaping convention.

The runner does not alter any proof, upstream exporter, or Nanoda kernel source.
The Python export scan checks coverage and policy; it is **not** a type checker.
Nanoda must independently check every declaration in the resulting export. Its
Nat and String extensions are enabled, with the rc6 builtin prerequisite list.
The only permitted axioms are `propext`, `Quot.sound`, and `Classical.choice`;
unpermitted axioms cause an error even if unused. There is no permissive fallback.

Historical macOS `.olean` hashes are not required to match freshly built Linux
artifacts. The source inventory is bound to the passed audit selected by tools-lock.json, while the
artifacts used for each new run are hashed immediately before export and checked
again afterwards. Any source or module-set drift requires a new full audit and
an explicit lock update. A fresh Lean audit from the root wrapper does not
silently change this binding.

Dependency checkouts must match every exact revision in `lake-manifest.json`,
with no changes to tracked source files, before building and after checking.
Existing compiled dependency caches and the Lean/exporter loading path remain
part of the trusted input provenance: source hashes alone do not attest that a
cached `.olean` was derived from those sources. Nanoda rechecks the proof terms
actually exported, while correspondence between those terms and source-level
statements also requires the separate comparator workflow. This runner does not
claim to replace that comparison.

## Pins and primary-source review

| Component | Pinned version |
| --- | --- |
| Lean | `leanprover/lean4:v4.29.0-rc6` |
| lean4export | `71f41350675895dda791b8ff9c1dfb77d18b3585` |
| Export format | NDJSON `3.1.0` |
| Nanoda | `418320295890faed83a96fd97907b12a3b6728c2` |
| Rust | `1.93.1` |

The exact exporter pin declares the matching Lean toolchain and format `3.1.0`; the exact Nanoda parser accepts formats `>= 3.1.0, < 3.2.0`. The successful archived full run establishes end-to-end compatibility for the bound source snapshot. The earlier API/driver-only [compilation check](compilation-check.json) remains historical preparation evidence and is distinct from the full export and independent kernel execution.

Primary sources reviewed:

- [lean4export CLI and recursive export implementation](https://github.com/leanprover/lean4export/tree/71f41350675895dda791b8ff9c1dfb77d18b3585)
- [Nanoda parser at the pinned commit](https://github.com/ammkrn/nanoda_lib/blob/418320295890faed83a96fd97907b12a3b6728c2/src/parser.rs)
- [Nanoda configuration and checking behavior](https://github.com/ammkrn/nanoda_lib/blob/418320295890faed83a96fd97907b12a3b6728c2/README.md)
- [Rust 1.93.1 release](https://github.com/rust-lang/rust/releases/tag/1.93.1)

The runner uses the unmodified Nanoda commit with no performance patches.
Performance or compatibility failures remain failures to investigate, without
relaxing the kernel or the axiom policy.

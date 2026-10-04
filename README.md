# Mixed-state quantum cloning

Lean proofs for **all 27 named results** in the frozen reference snapshot: known- and unknown-spectrum cloning, projector-state optimality, purify–clone–trace comparisons, and supporting estimates. Read the [paper](https://arxiv.org/abs/2609.35986); the audited manuscript snapshot is identified in [SOURCE.json](formalization/SOURCE.json).

Read the [proof wiki](https://jwang226.github.io/Cloning/): twelve informal proof guides, all 27 named results, exact Lean statements, and searchable source. Each result links to its guide and Lean declarations. The [bundled pages](docs/index.html) also work offline. The [proof map](formalization/PROOF_MAP.md) records assumptions, fidelity conventions, dimensions, and limits.

## Verification

All three checks passed against the same pinned source snapshot:

- **Lean:** 982 implementation modules; complete axiom audit of **14,345 project constants**, using only `propext`, `Classical.choice`, and `Quot.sound`. [Audit record](formalization/verification/kernel-compatible-pass/run.json).
- **Comparator:** all **27 explicit statements** and their proof dependencies matched; axiom checking and Lean kernel replay passed. The recorded run used trusted local execution without a sandbox. [Run record](formalization/verification/comparator/records/20261004T055545.209379Z/run.json).
- **Nanoda:** the pinned, unmodified independent Rust kernel checked **83,433 exported declarations**, covering every project constant and its dependencies. [Run record](formalization/verification/nanoda/records/20261004T055629.624926Z/run.json).

The proof library contains no `sorry` or additional axioms. Comparator's deliberate challenge placeholders are outside that library. [Machine-readable status](formalization.yaml) and the [compiler compatibility report](formalization/verification/kernel-compatibility.md) preserve the scope and historical evidence.

## Reproduce

Linux or macOS requires Git, curl, tar, Python 3.10+, a C toolchain, [elan](https://github.com/leanprover/elan), and network access. Lean **4.29.0-rc6** and Mathlib are fixed by the repository's toolchain and dependency manifest.

```sh
git clone https://github.com/JWang226/Cloning.git
cd Cloning/formalization
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build All
python3 scripts/check_checkpoint.py
```

The checkpoint validates saved evidence. For a fresh complete axiom audit:

```sh
python3 scripts/audit.py --jobs 3
```

From the same `formalization/` directory, run Comparator's default sandboxed mode on Linux with Landlock, an unprivileged account, and **Go 1.25.0**:

```sh
bash verification/comparator/run.sh
```

On macOS, explicitly select trusted local execution, which provides **no sandbox**:

```sh
bash verification/comparator/run.sh --trusted-local
```

For Nanoda on either platform, install Rustup/Cargo and the pinned **Rust 1.93.1** toolchain:

```sh
rustup toolchain install 1.93.1 --profile minimal
bash verification/nanoda/run.sh --run --threads 1
```

Both runners fetch pinned tools, retain logs, and reject source drift. Full checks can require substantial memory and time. See [Comparator details](formalization/verification/comparator/README.md), [Nanoda details](formalization/verification/nanoda/README.md), and [exact tool pins](formalization/verification/tools-lock.json).

## Scope and attribution

Degenerate-spectrum and fixed-rank formulas remain conjectures; the exact all-density asymptotic optimum remains open. See [scope and progress](formalization/PROGRESS.md).

[Source provenance](formalization/EXTERNAL_RESOURCES.json) and the adapted Physlib [license](formalization/PHYSLIB-LICENSE.txt) are preserved. Documentation and verifier organization were inspired by [Anthropic's FLT project](https://github.com/anthropics/fermats-last-theorem).

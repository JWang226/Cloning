# Mixed-state quantum cloning

Lean proofs for **all 27 named results** in the frozen reference snapshot: known- and unknown-spectrum cloning, projector-state optimality, purify–clone–trace comparisons, and supporting estimates. Read the [paper](https://arxiv.org/abs/2609.35986); the audited manuscript snapshot is identified in [SOURCE.json](formalization/SOURCE.json).

[Proof website](https://jwang226.github.io/Cloning/) ·
[Paper → Lean proof](https://jwang226.github.io/Cloning/correspondence.html) ·
[Dependency map](https://jwang226.github.io/Cloning/dependencies.html) ·
[Verification guide](https://jwang226.github.io/Cloning/verification.html)

The guides connect paper sections and informal arguments to exact Lean declarations. The [proof map](formalization/PROOF_MAP.md) records the correspondence, assumptions, and scope; the [bundled website](docs/index.html) also works offline. A focused [statement review](https://jwang226.github.io/Cloning/statement-review.html) checks Theorems 1.1–1.3 and explains the projector cloner’s different finite coupling construction.

## How it was verified

All three checks passed against the same pinned source snapshot:

- **Lean:** 982 implementation modules; shared axiom audit of **14,344 project constants**, with aggregate axioms `propext`, `Classical.choice`, and `Quot.sound`. [Audit record](formalization/verification/cleanup-pass/run.json).
- **Comparator:** all **27 explicit statements** and their proof dependencies matched; axiom checking and Lean kernel replay passed. The recorded run used trusted local execution without a sandbox. [Run record](formalization/verification/comparator/records/20261007T042117.504957Z/run.json).
- **Nanoda:** the pinned, unmodified independent Rust kernel checked **83,432 exported declarations**, covering every project constant and its dependencies. [Run record](formalization/verification/nanoda/records/20261007T042711.164065Z/run.json).

An [earlier macOS run](formalization/verification/shared-audit-check.json) with compiled caches passed the shared Lean build + audit in **36 seconds**, versus **65 minutes** for the previous auditor, with identical coverage and aggregate axioms at that earlier source snapshot. The [earlier combined run](formalization/verification/reproducer-check.json) records all three checkers.

The [cleanup and elaboration report](ELABORATION_REPORT_2026-10-06.md) records both tests and repeated compiler controls; the [dead-code report](DEAD_CODE_REPORT_2026-10-06.md) records the preceding sweep. Current verification above is bound to the cleanup sources.

The proof library contains no `sorry` or additional axioms. Comparator's deliberate challenge placeholders are outside that library. [Machine-readable status](formalization.yaml) and the [compiler compatibility report](formalization/verification/kernel-compatibility.md) preserve the scope and historical evidence.

## Check it yourself

Use **macOS or Linux**, [elan](https://github.com/leanprover/elan), Git, curl, tar, Python 3.10+, native C/C++ compiler tools, and [Rustup](https://rustup.rs/) for Nanoda. Initial setup needs internet access and space for dependencies. The wrapper prepares the pinned tools and saves fresh logs for each run.

```sh
git clone https://github.com/JWang226/Cloning.git
cd Cloning
bash scripts/verify.sh all
```

Success ends with **`VERIFICATION PASSED: all`**. Any failed check returns a nonzero exit code. Build time depends on caches and hardware; fresh logs and reports are saved in the printed `.verify-work/run-*` directory. To run one layer from the repository root:

```sh
bash scripts/verify.sh lean        # build + complete axiom audit
bash scripts/verify.sh comparator  # 27 statements + Lean kernel replay
bash scripts/verify.sh nanoda      # independent Rust kernel
```

These commands run trusted local checks without a sandbox. The [Comparator guide](formalization/verification/comparator/README.md) also gives the Linux sandboxed procedure. Existing reports document earlier runs; the commands above execute new checks.

Lean is pinned to **4.29.0-rc6**, dependencies by the [Lake manifest](formalization/lake-manifest.json), and checker tools by [tools-lock.json](formalization/verification/tools-lock.json). The wrapper installs pinned Rust **1.93.1** through Rustup. Keep these pins; do not run `lake update`. See the [Nanoda guide](formalization/verification/nanoda/README.md) for its exact export scope.

## Scope and attribution

Degenerate-spectrum and fixed-rank formulas remain conjectures; the exact all-density asymptotic optimum remains open. See [scope and progress](formalization/PROGRESS.md).

[Source provenance](formalization/EXTERNAL_RESOURCES.json) and the adapted Physlib [license](formalization/PHYSLIB-LICENSE.txt) are preserved.

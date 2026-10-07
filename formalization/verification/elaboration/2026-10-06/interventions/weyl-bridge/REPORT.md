# Measured Weyl projector conversion cleanup

Decision: accept the single local equality rewrite in `integral_weighted_characteristic`.

The original `change` compared `rankOneOperator x x` with the `vectorProjector x` requested by `traceClass_functional_ext`. The named trace labels matched this exact source expression; their expensive definitional comparison descended through CFC and chosen Hilbert-basis data. Rewriting the equality between the bundled projectors first avoids that comparison. The public statement, namespace, hypotheses, imports and options are unchanged.

The ignored proof-body `sorry` diagnostic reduced exclusive tactic execution from 105 s to 0.929 s. It established proof-body cost and is not part of the accepted source. Both A/B arms used the same entry path, saved setup module name, imported artifacts, threads=2 and disabled artifact cache. Traced A/B runs used pp=false in both arms; the repository before/after profiles use pp=true. The separate bare pairs omitted all profile/trace/stats flags.

| Mode | Arm | Run | Wall s | User CPU s | System CPU s | Total CPU s | Max-process RSS KiB |
|---|---|---:|---:|---:|---:|---:|---:|
| profile | A | 1 | 112.98 | 111.24 | 3.07 | 114.31 | 2,927,648 |
| profile | B | 1 | 10.98 | 8.70 | 2.56 | 11.26 | 2,886,544 |
| profile | A | 2 | 113.24 | 112.47 | 3.28 | 115.75 | 2,860,272 |
| profile | B | 2 | 8.39 | 9.22 | 2.14 | 11.36 | 2,878,288 |
| profile | A | 3 | 110.13 | 111.55 | 2.68 | 114.23 | 2,896,192 |
| profile | B | 3 | 7.75 | 9.15 | 2.21 | 11.36 | 2,934,976 |
| bare | A | 1 | 106.89 | 107.56 | 2.49 | 110.05 | 2,879,680 |
| bare | B | 1 | 6.55 | 7.67 | 2.12 | 9.79 | 2,920,336 |
| bare | A | 2 | 106.83 | 107.53 | 2.36 | 109.89 | 2,917,984 |
| bare | B | 2 | 6.62 | 7.51 | 2.11 | 9.62 | 2,929,904 |
| bare | A | 3 | 107.62 | 108.01 | 2.57 | 110.58 | 2,919,808 |
| bare | B | 3 | 7.53 | 7.02 | 2.12 | 9.14 | 2,924,496 |

Profile medians: wall 112.98 → 8.39 s; GNU total CPU 114.31 → 11.36 s; exclusive tactic execution 106 → 1.48 s. Bare medians: wall 106.89 → 6.62 s (93.8% lower); GNU total CPU 110.05 → 9.62 s (91.3% lower). RSS stayed essentially unchanged; no memory improvement is claimed. These are this file’s controlled measurements, not a prediction of the full-build change.

All 12 A/B processes exited 0, with stable source, configuration, direct import hashes, mapped transitive artifact metadata, setup and build trace. The tracked source remained unchanged throughout measurement; it was updated only after the keep verdict. No imported package compilation or artifact writes were requested.

## Provenance

Baseline source commit: `cbb2fd2007ae367e201d4a6ac7c069899db90dbd`.
Experiment context commit: `80e4b7ca1aa43969f85105171bfd80bf662d6b32`.
A source SHA-256: `c3ad276535f7e0b776dae495c8a0a8e42e9967d8a36f8ed7d5a8ef55193ac80d`.
B source SHA-256: `e1413287599caab0c36d5cf8625f327b319f75c097fe6cc33d4351f22cff5dc7`.
Setup SHA-256: `7398bb862731937c44e19ae7c44ceaddba2e487349b4e5739978e15bcbc015c6`.
Harness SHA-256: `968687bc80c9f9ecdf373a74fa3409be5ee6c6af4dce633f78e63f13725bc79a`.

Raw commands, environment, start/end UTC, source snapshots and import guards are in `profiles.json`, `bare.json`, `plan.json` and each import-context JSON. `summary.json` includes only diagnostic and A/B traced runs; `verdict.json` gives all controlled measurements. `candidate.patch` is the exact accepted one-line change.

## Repeat one saved arm

Copy A or B into the stable ignored entry path before using its recorded command; do not execute the diagnostic as a verification of the accepted source. For example:

```bash
cp /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/weyl-bridge-ab/B.source.lean.txt /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/weyl-bridge-ab/WeylIdlerUniqueness.lean
env LEAN_NUM_THREADS=2 LAKE_ARTIFACT_CACHE=false /opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/weyl-bridge-ab/REPEAT-B-bare.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/weyl-bridge-ab/setup.json /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/weyl-bridge-ab/WeylIdlerUniqueness.lean
```

Run from the `formalization` directory with the pinned toolchain and existing package artifacts. Use a fresh output location for new evidence rather than overwriting these raw files. Full-library checks, public endpoint checks and fresh axiom/exporter verification remain the parent campaign’s final checks.

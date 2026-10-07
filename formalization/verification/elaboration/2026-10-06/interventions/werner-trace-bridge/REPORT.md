# Measured Werner trace conversion cleanup

Decision: accept the explicit trace equality chain in `wernerOutput_trace_one`.

The original `change ... at htp` compared the analytic trace used by the channel with `traceCLM`, descending through CFC and chosen Hilbert-basis data. The before trace attributed 36.7 s to this exact change in the named theorem. The replacement composes `traceCLM_apply(output)`, the channel’s `trace_preserving(input)`, and `traceCLM_apply(input).symm`, establishing the same local equality using named API lemmas. No public statement, namespace, hypotheses, imports or options change.

The ignored proof-body `sorry` diagnostic reduced exclusive tactic execution from 39.4 s to 2.51 s. It established proof-body cost and is not part of the accepted source. Both A/B arms used the same entry path, saved setup module name, imported artifacts, threads=2 and disabled artifact cache. Traced A/B runs used pp=false in both arms; repository before/after profiles use pp=true. Bare pairs omitted all profile/trace/statistics flags.

| Mode | Arm | Run | Wall s | User CPU s | System CPU s | Total CPU s | Max-process RSS KiB |
|---|---|---:|---:|---:|---:|---:|---:|
| profile | A | 1 | 43.01 | 45.74 | 2.19 | 47.93 | 3,149,232 |
| profile | B | 1 | 7.38 | 8.41 | 2.10 | 10.51 | 2,875,744 |
| profile | A | 2 | 42.73 | 45.35 | 2.09 | 47.44 | 3,044,480 |
| profile | B | 2 | 7.26 | 8.44 | 1.97 | 10.41 | 2,909,376 |
| profile | A | 3 | 42.79 | 45.38 | 2.16 | 47.54 | 3,108,720 |
| profile | B | 3 | 7.24 | 8.46 | 1.99 | 10.45 | 2,922,880 |
| bare | A | 1 | 39.35 | 40.92 | 2.02 | 42.94 | 2,896,656 |
| bare | B | 1 | 6.65 | 6.83 | 2.02 | 8.85 | 2,891,584 |
| bare | A | 2 | 39.67 | 41.19 | 2.21 | 43.40 | 2,863,184 |
| bare | B | 2 | 6.74 | 6.85 | 2.03 | 8.88 | 2,895,408 |
| bare | A | 3 | 39.54 | 41.10 | 2.04 | 43.14 | 2,862,544 |
| bare | B | 3 | 6.78 | 6.97 | 2.10 | 9.07 | 2,894,304 |

Profile medians: wall 42.79 → 7.26 s; GNU total CPU 47.54 → 10.45 s; exclusive tactic execution 38.80 → 2.46 s. Bare medians: wall 39.54 → 6.74 s (82.9% lower); GNU total CPU 43.14 → 8.88 s (79.4% lower). Profile RSS medians decreased, but bare controls did not reproduce a decrease; no memory improvement is claimed. These are this file’s controlled measurements, not a prediction of the full-build change.

All 12 A/B processes exited 0 with stable source, configuration, direct import hashes, mapped transitive artifact metadata, setup and build trace. Tracked Werner source remained unchanged throughout measurement and was updated only after the keep verdict. No imported package compilation or artifact writes were requested.

## Provenance

Baseline source commit: `cbb2fd2007ae367e201d4a6ac7c069899db90dbd`.
Experiment context commit (Weyl already accepted separately): `f66714d5f0b21c248696d833f35f86f364ae413a`.
A source SHA-256: `815e8e1962e901e11ae9fbd73bd3988bd0cc58ec6c953685b05fa25226aa17ea`.
B source SHA-256: `328dd36bde83e302e13d99f6168651cb90f5a10b39811339590e645822c5b30b`.
Setup SHA-256: `257a5dac9e7fe1bbab5b94c1ba93c2d89f6dab60d06e820de4773673e43324c5`.
Harness SHA-256: `157a0754b435b8e74bae29c73745d9b37b7d106bb8514e88ffe60965e2c5b670`.

Raw commands, selected environment, start/end UTC, snapshots and input guards are in `profiles.json`, `bare.json`, `plan.json` and each import-context JSON. `summary.json` includes the diagnostic and six paired traced runs; `verdict.json` gives all controlled measurements. `candidate.patch` is the exact accepted change. The all-994 source/API/config guard is saved as `../cleanup-api-source-guard.json`.

## Repeat one saved arm

Copy A or B into the stable ignored entry path before using its recorded command. The diagnostic is not a verification of accepted source. For example:

```bash
cp /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/werner-trace-bridge-ab/B.source.lean.txt /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/werner-trace-bridge-ab/WernerPhysicalPullback.lean
env LEAN_NUM_THREADS=2 LAKE_ARTIFACT_CACHE=false /opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/werner-trace-bridge-ab/REPEAT-B-bare.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/werner-trace-bridge-ab/setup.json /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/werner-trace-bridge-ab/WernerPhysicalPullback.lean
```

Run from the `formalization` directory with the pinned toolchain and existing package artifacts. Use fresh output paths for new evidence. Final full-library, public endpoint, axiom and exporter checks belong to the parent campaign.

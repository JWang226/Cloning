# Current semantic review

The [completion semantic review](completion-semantic-review.md) and [proof map](../PROOF_MAP.md) retain the original correspondence for all 27 named statements. Historical pass-specific reviews and audits remain unchanged.

The focused endpoint reviews for Theorems 1.1–1.3 preserve the original semantic judgment of 2026-10-06 against revision `d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999`. The same three Lean type/application probes were freshly re-executed on 2026-10-07 against `bcb3c208c0a47a9d905d71ec48ec107a0118db04`: [Known spectrum](semantic-pilot/cleanup-pass/cleanup-known-spectrum.md) · [Unknown spectrum](semantic-pilot/cleanup-pass/cleanup-unknown-spectrum.md) · [Projector states](semantic-pilot/cleanup-pass/cleanup-projector.md). All three passed with unchanged probe bytes and current proof/configuration inputs. This is probe revalidation, not a new full semantic review or external peer review.

The [current shared build/axiom audit](cleanup-pass/run.json) covers 982 implementation modules and 14,344 project roots. Its axiom report gives the aggregate union over roots and dependencies, without per-root attribution. [Comparator](comparator/status.json) passed the 27 explicit statements and their proof dependencies; [Nanoda](nanoda/status.json) independently checked all 83,432 exported declarations. These source-bound checker records are separate from the English paper correspondence judgments.

The selected shared audit has SHA-256 `cd6735524ed4f60d02fded4b846eaa349d36fc3d151df5768ddc5fcfe4ada61b`. The [saved-evidence replay](cleanup-checkpoint.json) confirms certificate integrity and exact current proof/configuration hashes without invoking Lean.

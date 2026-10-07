# Projector states — native probe revalidation

Fresh successful execution at 2026-10-07T04:39:43.237746+00:00 against cleanup revision `bcb3c208c0a47a9d905d71ec48ec107a0118db04`.
The selected shared audit run has SHA-256 `cd6735524ed4f60d02fded4b846eaa349d36fc3d151df5768ddc5fcfe4ada61b`.

The [original semantic review](https://github.com/JWang226/Cloning/blob/main/formalization/verification/semantic-pilot/projector.md) of revision `d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999` remains the source of the English correspondence judgment. This pass re-executes its unchanged successful Lean type/application probe and does not repeat the paper review or review every upstream proof. It is not external peer review.

The optimum and uniform attaining-channel limit match. Lean uses a different finite coupling construction from the one selected in the paper.

- Projectors are literal Hermitian idempotent matrices of rank r; their states are P/r. The minimax ranges over every quantum channel and every such projector.
- Physical dimension is D=r+k, so γ^(−r*k/2) is the paper’s γ^(−r(D−r)/2). Lean also includes k=0, the singleton boundary with value 1.
- Paper §4.2 selects a transportation-program minimizer. Lean constructs a coupling from overlapping densities, proves its exact marginals, and proves its cloner attains the optimum uniformly. Equality of the two finite constructions is not established.

The complete shared axiom audit reports the permitted aggregate union over all roots and dependencies. It does not assign a separate axiom set to these endpoints. Comparator and Nanoda supply separately recorded checker evidence.

```sh
cp formalization/verification/semantic-pilot/cleanup-pass/cleanup-projector.lean.txt /tmp/cleanup-projector.lean
(cd formalization && lake env lean -DautoImplicit=false /tmp/cleanup-projector.lean)
```

The accompanying run record binds the actual command, current source/configuration hashes, fresh output, unchanged probe bytes, selected audit, and exit status.

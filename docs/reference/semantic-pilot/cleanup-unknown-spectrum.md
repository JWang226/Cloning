# Unknown spectrum — native probe revalidation

Fresh successful execution at 2026-10-07T04:39:37.780698+00:00 against cleanup revision `bcb3c208c0a47a9d905d71ec48ec107a0118db04`.
The selected shared audit run has SHA-256 `cd6735524ed4f60d02fded4b846eaa349d36fc3d151df5768ddc5fcfe4ada61b`.

The [original semantic review](https://github.com/JWang226/Cloning/blob/main/formalization/verification/semantic-pilot/unknown-spectrum.md) of revision `d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999` remains the source of the English correspondence judgment. This pass re-executes its unchanged successful Lean type/application probe and does not repeat the paper review or review every upstream proof. It is not external peer review.

One spectrum-independent channel has the uniform limit in part (a). The minimax conclusion in part (b) retains the paper’s stronger condition on the spectral set.

- The channel depends on sample sizes and dimension, without taking the true spectrum, unitary, or compact set as an argument. Its exact covariance is separately proved.
- Part (a) permits every compact spectral set, including a singleton. Part (b) requires a nonempty compact set equal to the closure of its interior in the full trace-one affine hyperplane.
- Lean’s hd: 1≤d means physical dimension d+1≥2. The payoff uses root fidelity, and the limit includes the classical factor with exponent (D−1)/2.

The complete shared axiom audit reports the permitted aggregate union over all roots and dependencies. It does not assign a separate axiom set to these endpoints. Comparator and Nanoda supply separately recorded checker evidence.

```sh
cp formalization/verification/semantic-pilot/cleanup-pass/cleanup-unknown-spectrum.lean.txt /tmp/cleanup-unknown-spectrum.lean
(cd formalization && lake env lean -DautoImplicit=false /tmp/cleanup-unknown-spectrum.lean)
```

The accompanying run record binds the actual command, current source/configuration hashes, fresh output, unchanged probe bytes, selected audit, and exit status.

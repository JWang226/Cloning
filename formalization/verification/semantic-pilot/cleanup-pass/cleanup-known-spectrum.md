# Known spectrum — native probe revalidation

Fresh successful execution at 2026-10-07T04:39:25.318388+00:00 against cleanup revision `bcb3c208c0a47a9d905d71ec48ec107a0118db04`.
The selected shared audit run has SHA-256 `cd6735524ed4f60d02fded4b846eaa349d36fc3d151df5768ddc5fcfe4ada61b`.

The [original semantic review](https://github.com/JWang226/Cloning/blob/main/formalization/verification/semantic-pilot/known-spectrum.md) of revision `d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999` remains the source of the English correspondence judgment. This pass re-executes its unchanged successful Lean type/application probe and does not repeat the paper review or review every upstream proof. It is not external peer review.

The reviewed endpoints preserve root fidelity, optimization over all quantum channels, and the compact-uniform limit of the spectrum-dependent cloner.

- Lean uses physical dimension d+1 and a positive, strictly ordered, normalized SimpleSpectrum. The minimax definition chooses a channel before the unknown unitary.
- The attaining channel may depend on the known spectrum. Its uniform theorem gives one threshold for all spectra in a fixed compact set and all unitaries.
- The channel samples the exact target Young-label law. The review traces its sector construction and the internally constructed LAN witness; neither is an extra hypothesis of the endpoint.

The complete shared axiom audit reports the permitted aggregate union over all roots and dependencies. It does not assign a separate axiom set to these endpoints. Comparator and Nanoda supply separately recorded checker evidence.

```sh
cp formalization/verification/semantic-pilot/cleanup-pass/cleanup-known-spectrum.lean.txt /tmp/cleanup-known-spectrum.lean
(cd formalization && lake env lean -DautoImplicit=false /tmp/cleanup-known-spectrum.lean)
```

The accompanying run record binds the actual command, current source/configuration hashes, fresh output, unchanged probe bytes, selected audit, and exit status.

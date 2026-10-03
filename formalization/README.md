# Lean formalization of mixed-state cloning

Start with the [repository result index](../README.md#the-results) and [machine-readable status](../formalization.yaml). This package contains the 195-module checked library, ten result entry points, and `All.lean`.

```sh
lake exe cache get
lake build All
python3 scripts/check_checkpoint.py
```

For an individual result, use e.g. `lake build BosonicSeededOptimum`. For a fresh full axiom audit after building, use `python3 scripts/audit.py --jobs 3`.

The [verification instructions](scripts/README.md) explain the saved evidence and fresh-audit workflow. The [current progress report](PROGRESS.md) records the new constructions and remaining obligations. The original [detailed progress report](verification/seventh-pass/README.md) and [semantic audit](verification/seventh-pass/PROOF_AUDIT.md) are preserved byte-for-byte as historical checkpoint documents; their original local reproduction commands are superseded by the commands above.

The complete manuscript theorem remains conditional. See the [remaining mathematical inputs](../README.md#remaining-mathematical-inputs) for its precise limits.

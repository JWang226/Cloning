import Cloning.OrbitalSeededOptimum
import Cloning.MultimodeLeastNoise
import Cloning.BosonicAmplifierThermal

/-!
# Exact bosonic seeded fidelity optimum

The constructed amplifier has the exact thermal output and achieved mode factor. Every
correlated or coherent joint idler satisfies the full antitone product-observable bound,
and vacuum attains the exact orbitalValue optimum over all joint idler density states.
Universality over arbitrary displacement-covariant channels still requires Weyl
covariance, the arbitrary-idler representation theorem, and the composite-gain
reduction.

This public entry point adds no definitions or proofs. The declarations below locate the
principal result and its supporting statements in the checked library.
-/

#check Cloning.OrbitalSeededOptimum.isGreatest_payoff
#check Cloning.MultimodeLeastNoise.productObservable_moment_le
#check Cloning.BosonicAmplifier.stateFidelity_channel_gain

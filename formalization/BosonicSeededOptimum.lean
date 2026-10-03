import Cloning.OrbitalSeededOptimum
import Cloning.MultimodeLeastNoise
import Cloning.BosonicAmplifierThermal
import Cloning.WeylCovariantMultiplier
import Cloning.WeylMultimodeChannel

/-!
# Bosonic seeded optimum and the actual Weyl representation

The exact fidelity optimum over arbitrary joint idler density states is proved for
the constructed amplifier family. Actual one- and finite-multimode Weyl unitaries and
CPTP displacement channels have proved continuity, irreducibility, and fixed-character
eigenoperator classification. Covariant linear maps on bounded operators have scalar
Weyl multipliers. The CP/normality-to-idler representation, amplifier intertwining,
and composite-gain reduction remain separate from this algebraic multiplier theorem.

This entry point adds no definitions or proofs.
-/

#check Cloning.OrbitalSeededOptimum.isGreatest_payoff
#check Cloning.MultimodeLeastNoise.productObservable_moment_le
#check Cloning.BosonicAmplifier.stateFidelity_channel_gain
#check Cloning.MultimodeCoherent.displacement_commutant_scalar
#check Cloning.MultimodeCoherent.eigenoperator_eq_scalar_displacement
#check Cloning.MultimodeCoherent.covariant_linearMap_weyl_multiplier

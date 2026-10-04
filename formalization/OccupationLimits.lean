import Cloning.InfiniteOccupationStates
import Cloning.WernerPhysicalPullback
import Cloning.WernerPhysicalAgreement
import Cloning.GeneralCoherentChannels
import Cloning.UniformCoherentChannels
import Cloning.PCTGaussianAssembly
import Cloning.PCTPurificationChannelPhysical
import Cloning.PCTGlobalPhysical

/-!
# Physical Werner output, coherent limits, and PCT mixtures

Werner's full CPTP channel has its literal physical symmetric sandwich on arbitrary
symmetric input matrices. Its pure-product output converges to a thermal Fock state,
and pure product tensors admit compact-uniform two-way coherent comparison channels.
The full-environment Haar random-purification map is an actual finite CPTP channel,
with exact action on tensor powers. The complete full-environment protocol is an
actual state-independent global CPTP channel, agreeing with the literal physical
purification-Werner-partial-trace formula on every complex input matrix. Its output
converges to a Gaussian mixture of reduced tensor powers. Smaller rank-adapted
environments, full mixed-state Schur-block LAN, and the final PCT fidelity limit
remain separate.

This entry point adds no definitions or proofs.
-/

#check Cloning.GeneralSymmetricOccupation.wernerOutput_op
#check Cloning.GeneralSymmetricOccupation.occupationRecovery_wernerOutput
#check Cloning.GeneralSymmetricOccupation.physical_werner_traceNorm_limit
#check Cloning.GeneralCoherent.exists_twoWay_coherent_product_channels
#check Cloning.GeneralCoherent.twoWay_coherent_product_uniform_on_compact
#check Cloning.GeneralSymmetricOccupation.wernerChannel_physical_sandwich
#check Cloning.GeneralSymmetricOccupation.wernerChannel_completelyPositive
#check Cloning.GeneralSymmetricOccupation.wernerChannel_pure_traceClass_agrees
#check Cloning.GeneralSymmetricOccupation.wernerChannel_pure_output
#check Cloning.GeneralSymmetricOccupation.wernerChannel_thermal_limit
#check Cloning.PCT.exists_pct_product_mixture
#check Cloning.PCTPurificationChannel.haarPurificationChannel
#check Cloning.PCTPurificationChannel.haarPurificationChannel_tensorPower
#check Cloning.PCTPurificationChannel.haarPurificationChannel_physical
#check Cloning.PCTPurificationChannel.physical_pct_eq_reducedWerner
#check Cloning.PCTPurificationChannel.physical_pct_gaussian_product_mixture
#check Cloning.PCTGlobal.channel
#check Cloning.PCTGlobal.channel_matrix_apply
#check Cloning.PCTGlobal.channel_apply
#check Cloning.PCTGlobal.channel_tensorPower
#check Cloning.PCTGlobal.channel_gaussian_product_mixture

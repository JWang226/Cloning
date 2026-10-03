import Cloning.InfiniteOccupationStates
import Cloning.WernerPhysicalPullback
import Cloning.WernerPhysicalAgreement
import Cloning.GeneralCoherentChannels
import Cloning.UniformCoherentChannels

/-!
# Physical Werner output and uniform coherent-product limits

Werner’s full CPTP channel is constructed on arbitrary symmetric input matrices and
proved equal to the physical dimension-ratio sandwich. Its pure-product output is identified with
its occupation law through a constructed CPTP recovery, and converges in trace norm to
the thermal Fock operator. Literal normalized complex product tensors admit actual
two-way CPTP comparison channels with multimode coherent states, uniformly on compact
amplitude sets in every finite dimension. These pure-state comparison results do not
supply mixed-state Schur-block LAN or the remaining finite-sample PCT identification.

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

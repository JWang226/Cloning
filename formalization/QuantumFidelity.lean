import Cloning.InfiniteChannelFidelity
import Cloning.InfiniteFidelityContinuity
import Cloning.InfiniteFidelityRegularized

/-!
# Dimension-independent quantum fidelity estimates

Data processing, trace-distance continuity, positive deletion, and weighted fidelity are
proved for actual positive trace-class operators, including singular inputs. The
unbounded-inverse witness version retains an explicit uniform regularized inverse-moment
premise; model-specific channels and approximation errors are not supplied by these
general inequalities.

This public entry point adds no definitions or proofs. The declarations below locate the
principal result and its supporting statements in the checked library.
-/

#check Cloning.InfiniteFidelity.fidelity_data_processing
#check Cloning.InfiniteFidelity.stateFidelity_continuity
#check Cloning.InfiniteFidelity.fidelity_deletion_bound
#check Cloning.InfiniteFidelity.fidelity_sq_le_of_regularized_inverse_moment

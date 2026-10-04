# Semantic review of the eleventh-pass constructions

These read-only mathematical reviews supplement compilation and the complete compiled-constant audit. They concern the exact theorem statements, including hypotheses and quantifier order. They do not certify the still-incomplete physical mixed-state cloning theorem. All work remains local.

## Arbitrary-partition tensors and physical PBW estimates

The tensor-product reviewer independently checked the antisymmetric-column construction, literal tensor concatenation, and the partition wrapper. The constructed vector lives in the actual tensor register with exactly the partition's number of boxes. A nonzero computational coefficient justifies normalization. Every raising generator annihilates it, and the Cartan eigenvalues are exactly the partition entries. Empty alphabets and zero boxes are included. No irreducible representation or Schur decomposition is assumed or claimed by this construction.

The independent reviewer also checked the entire cyclic-filtration, occupancy, root-bound, normalized-CCR, and PBW chain. The filtration is the span of all lowering words of bounded total positive-root height, not a shifted ambient occupancy cutoff. Its level zero is precisely the highest-vector span. Raising lowers the cutoff and annihilates level zero; any retained creator raises height by at most the fixed alphabet dimension. Computational occupancy bounds give the Cartan defect, and adjoint recursion gives raw-root norms even when a highest-weight gap is zero. The normalized oscillator coordinates require positive retained gaps.

For total height R and smallest retained gap δ>0, the diagonal CCR defect is at most 2R/δ and the cross-root defect is at most sqrt((R+1)/δ + 2R(R+1)/δ²). The normalization inequality is derived for the two actual gaps. The commutator signs and root orientations were checked. Neither a CCR nor a local operator-norm bound is inserted as a hypothesis in the partition PBW endpoint.

Words of length at most L fit in height Ld. The threshold δ≥2(Ld+1) makes the combined error at most one, as required by the earlier abstract PBW estimate. Injectivity of the selected-root map gives the correct Kronecker term, and factorial normalization gives one exactly for words related by permutation. All highest-vector, vacuum, cutoff, and local-CCR premises are discharged for the constructed partition tensors.

The Gram-limit theorem permits varying partitions and tensor Hilbert spaces, but fixes the alphabet, retained roots, and words. A fixed finite family with distinct occupations has Gram matrix tending to the identity as retained gaps diverge. The determinant therefore tends to one and is eventually nonzero, proving linear independence in the actual, possibly varying tensor registers. This is not a statement of physical Schur identification, spanning of a whole irreducible sector, or LAN. The present constants do not justify a polynomially growing cutoff.

## Actual global full-environment PCT channel

The PCT author and root independently reviewed the channel assembly and fixed-coordinate Werner transport. The finite Kraus lift acts on every complex matrix and has actual finite-ancilla complete positivity and trace preservation. The Haar moment, its positive square root, and the purification channel output have the proved symmetric support; no support premise is supplied externally.

The global construction composes Haar purification, complement-repaired isometric recovery, the actual occupation Werner channel, physical re-embedding, regrouping, and partial trace. A fixed computational frame depends only on the alphabet and its cardinality, never on the unknown density matrix. Recovery followed by re-embedding is exactly the identity on every Haar output.

The arbitrary-input bridge inserts the identity on the entire residual tensor register. It does not replace that identity with an occupation-space identity. Word concatenation and its adjoint use the correct n/r coordinates, including zero lengths. The dimension factor is the same binomial ratio as the literal physical sandwich. The equality is proved for every complex matrix, then every trace-class input, and finally tensor-power states. The resulting Gaussian product-mixture theorem is therefore about an actual state-independent global CPTP output.

This closes the former global downstream CPTP proviso for the full environment. The environment dimension remains the system dimension. The smaller rank-adapted protocol and the final physical fidelity limit are not claimed.

## Mixed channels, fidelity, and statistical transfer

Root reviewed all-input quantum-to-hybrid and hybrid-to-quantum interfaces, composition, preparation, integration, norm bounds, and the forward fidelity proof. The maps are bounded complex-linear maps between the actual trace-class space and operator-valued L1, with finite-ancilla CP and trace preservation on all complex inputs. Positive-input norm identities and quantum-to-hybrid contraction are proved. Positive simple-field density supplies a reverse norm bound without a measurable Jordan decomposition.

Forward fidelity monotonicity transports a single attained quantum 2-by-2 block witness, uses pointwise positivity almost everywhere, and integrates its trace objective. No pointwise measurable optimizer is required. The reverse-channel proof was independently read by the mixed-channel author and root: positive integrable simple fields approximate arbitrary positive L1 classes, finitely many fibre witnesses form an integrable block, mixed CP and TP give the bound, and continuity passes to the limit. Vanishing of the witness at the zero pair is used for finite-measure support. Off-diagonal adjoint compatibility is derived from block positivity. The measure and Hilbert spaces are arbitrary.

The transferred competitor T∘M∘S is an actual hybrid channel on its whole input space. Its fidelity error is sqrt(δ)+sqrt(η), with no dimension, competitor, or channel-norm factor. The minimax theorem allows approximation bounds almost everywhere under each prior, so a compact-supported prior requires control only on its window. The Gaussian converse fixes the comparison maps by sample size before the window, allows sample-dependent quantum Hilbert spaces, first takes the sample-size limit at each fixed window, and then the expanding-prior limit. It uses the already proved optimized Gaussian value. Physical approximation bounds and actual mixed-state LAN constructions remain explicit inputs; this converse does not manufacture them.

## Gaussian covariance, orbital output, and normalization

The mixed-channel author and root independently reviewed the actual purification-frame characteristic integral, its joint classical/orbital specialization, the random-displacement output, and the normalization/remainder identities. Full orthonormal-frame Parseval gives the tangent covariance. Disjoint diagonal and off-diagonal computational entries give the joint characteristic exponent directly; Gaussian covariance and independence are not assumptions.

With v=γ−1, the classical covariance is 2v(diag(p)−ppᵀ), while orbital pair i<j has circular variance v(p_i+p_j)/(p_i−p_j). The factors of two agree with the classical characteristic exponent and with the thermal Weyl width. For q=p_j/p_i, the added circular variance is v(1+q)/(1−q). Adding it to the seed width gives (2γ−1) times that width, corresponding to Thermal.pct.

The stronger orbital endpoint integrates the displacements derived from the actual, common purification-frame tangent. It uses the proved joint characteristic and Weyl characteristic injectivity to obtain a product thermal trace-class operator. It does not assume a product pushforward law. Integrability follows from continuity and the displacement trace-norm isometry. This endpoint uses a strictly decreasing positive spectrum, γ>1, a complete frame anchored at the Schmidt purification, and an equivalence indexing all orbital pairs.

The normalized tangent vector uses its actual Hilbert–Schmidt energy. Norm one requires a normalized nonnegative spectrum and complex orthogonality to the reference purification. The exact quadratic remainder is an algebraic identity; by itself it is not an exact local spectral chart, an inverse-chart estimate, or a mixed-state LAN theorem. The joint hybrid comparison density/convolution and its final fidelity still require proof.

## Verification boundary

Every new branch compiled and its sampled endpoints used only `propext`, `Classical.choice`, and `Quot.sound`. The full eleventh-pass audit **passed** on `2026-10-03T16:18:55.910746+00:00`: **349 implementation modules, 3,075 source theorem/lemma declarations and 6,717 unique compiled project constants** (6,736 raw exports before deduplication). All three full-environment workers returned zero. The source placeholder scan passed; there were no unexpected axioms, missing modules, missing reports or conflicting reports. Source/dependency and compiled-artifact hashes remained unchanged. The [completion record](eleventh-pass/run.json) and raw reports preserve the complete evidence. Earlier checkpoint archives and the historical audit engine are unchanged.

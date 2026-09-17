import Atlas.Fischer.TensorFoundations
import Atlas.Fischer.TensorPointContractions
import Atlas.Fischer.TensorOctadSigns
import Atlas.Fischer.TensorOctadContractions
import Atlas.Fischer.OctadicConstruction
import Atlas.Fischer.OctadicGeometry
import Atlas.Fischer.SignedOctadPresentation
import Atlas.Fischer.ConwayParker
import Atlas.Fischer.WittDuads
import Atlas.Fischer.WittDistributions
import Atlas.Combinatorics.FourLevelMoments
import Atlas.Fischer.RootCovariance
import Atlas.Fischer.Roots
import Atlas.Fischer.RootRigidity
import Atlas.Fischer.CubicSymmetry
import Atlas.Fischer.AxisProductCoefficients
import Atlas.Fischer.CoordinateEvaluation
import Atlas.Fischer.OctadCubicCoefficients
import Atlas.Fischer.OctadCubicSigns
import Atlas.Fischer.CubicForm
import Atlas.Fischer.ProductCommutativity
import Atlas.Fischer.RootPhases
import Atlas.Fischer.ScalarAutomorphisms
import Atlas.Fischer.CocodeReflectionRepresentation
import Atlas.Fischer.ParkerCoordinateFaithfulness
import Atlas.Fischer.ParkerOctadSignFaithfulness
import Atlas.Fischer.ParkerStandardKernel
import Atlas.Fischer.ParkerSignNormalForm
import Atlas.Fischer.ParkerStandardAutomorphisms
import Atlas.Fischer.ParkerCoordinateAction
import Atlas.Fischer.SignedMonomialGeometry
import Atlas.Fischer.ParkerOctadProductAction
import Atlas.Fischer.ParkerMonomialData
import Atlas.Fischer.ParkerSignedOctadAction
import Atlas.Fischer.ParkerStandardParity
import Atlas.Fischer.CocodeInvolutions
import Atlas.Fischer.CocodeCoordinates
import Atlas.Fischer.BasicCocodeComparison
import Atlas.Fischer.ParkerStandardOrder
import Atlas.Fischer.ParkerStandardSurjectivity
import Atlas.Fischer.ParkerMathieuLiftExistence
import Atlas.Fischer.BasicRootMaps
import Atlas.Fischer.BasicRoots
import Atlas.Fischer.AxisSums
import Atlas.Fischer.ProductMaps
import Atlas.Fischer.ParkerCenter
import Atlas.Fischer.ParkerTripleRadical
import Atlas.Fischer.ParkerAlgebraRepresentation
import Atlas.Fischer.ParkerMultiplicativity
import Atlas.Fischer.ParkerProductInvariance
import Atlas.Fischer.ParkerOctadAction
import Atlas.Fischer.ParkerSignedProductTable
import Atlas.Fischer.ParkerAxisAction
import Atlas.Fischer.SemilinearAlgebraAutomorphisms
import Atlas.Fischer.ReflectingRoots
import Atlas.Fischer.ParkerRightAction
import Atlas.Fischer.Scalars
import Atlas.Fischer.ScalarGeometry
import Atlas.Fischer.CoordinateSpace
import Atlas.Fischer.SignedOctads
import Atlas.Fischer.Cocode
import Atlas.Fischer.ParkerFactorSet
import Atlas.Fischer.ParkerOrderedFactorSet
import Atlas.Fischer.ParkerGolayFactorSet
import Atlas.GroupTheory.PrimitiveConjugateGenerators
import Atlas.GroupTheory.InvolutiveFactorSwap
import Atlas.GroupTheory.InvolutiveNormalFactors
import Atlas.GroupTheory.IndexTwoInvariantNormals
import Atlas.GroupTheory.PrimitiveIndexTwoSimplicity
import Atlas.Fischer.ParkerBinaryDetermination
import Atlas.Fischer.ParkerGolayIdentities
import Atlas.Fischer.ParkerGolaySquareCommutator
import Atlas.Fischer.ParkerLoopIdentities
import Atlas.Fischer.ParkerLoopLifts
import Atlas.Fischer.ParkerCodeAction
import Atlas.Fischer.GolayPolarization
import Atlas.Fischer.OctadProducts
import Atlas.Fischer.CoordinateProduct
import Atlas.Fischer.ProductTable
import Atlas.Fischer.WittParameters
import Atlas.Fischer.WittIntersectionMoments
import Atlas.Algebra.BinaryCocycleSplitting
import Atlas.Combinatorics.BlockExtensionCount
import Atlas.Combinatorics.SubblockIncidenceCount
import Atlas.Sporadic.Janko2Construction
import Atlas.Conway.IcosianAlternatingConwayProduct
import Atlas.Conway.IcosianIntegralScalarCompatibility
import Atlas.Lattices.IcosianAxisDirectSum
import Atlas.Conway.IcosianProjectiveAngles
import Atlas.Conway.IcosianSixSuborbits
import Atlas.Conway.IcosianCoordinateAxisOrbits
import Atlas.Conway.IcosianAxisNormInvariant
import Atlas.Conway.IcosianSimplicity
import Atlas.Conway.IcosianAxisSuborbitLinks
import Atlas.Conway.IcosianReflectionSwaps
import Atlas.Conway.IcosianFullMonomialCentralizer
import Atlas.GroupTheory.FrameReflectionCommutator
import Atlas.Conway.IcosianAxisTransitionImages
import Atlas.Conway.IcosianOrder
import Atlas.Conway.IcosianPointNormalizations
import Atlas.Conway.IcosianLocalDOrbit
import Atlas.Conway.IcosianLocalBOrbit
import Atlas.Conway.IcosianLocalAOrbit
import Atlas.Conway.IcosianRootLocalOrbits
import Atlas.Conway.IcosianFiveAxisFramesCount
import Atlas.Conway.IcosianRootFrameStabilizer
import Atlas.Conway.IcosianLocalGeometryTransport
import Atlas.Conway.IcosianRootFrameAction
import Atlas.Conway.IcosianFrameCountInterface
import Atlas.Conway.IcosianFiveAxisFrames
import Atlas.Conway.IcosianAxisCompletion
import Atlas.Conway.IcosianCentralizerFinite
import Atlas.Conway.IcosianScalarFaithfulness
import Atlas.Lattices.IcosianHermitianIntegral
import Atlas.Conway.IcosianReflectionIsometries
import Atlas.Algebra.IcosianModuloTwoCoordinates
import Atlas.Algebra.IcosianNormOneReductionSurjective
import Atlas.Algebra.IcosianModuloTwoQuotient
import Atlas.Algebra.IcosianRightIdealMaximal
import Atlas.Algebra.IcosianGoldenModule
import Atlas.Algebra.IcosianReductionConjugation
import Atlas.Algebra.IcosianDivision
import Atlas.Codes.IcosianMatrixGlueStabilizer
import Atlas.Mathieu.TernaryWittMathieuAction
import Atlas.Codes.TernaryGolaySupports
import Atlas.Lattices.EisensteinCongruence
import Atlas.Codes.TernaryGolayQuotient
import Atlas.Sporadic.Conway3Simplicity
import Atlas.Sporadic.Conway3Construction
import Atlas.Sporadic.McLaughlin
import Atlas.Sporadic.McLaughlinGraph
import Atlas.Sporadic.Conway3Maximality
import Atlas.Sporadic.Conway3Triangles
import Atlas.Sporadic.Conway3
import Atlas.Sporadic.Conway2Construction
import Atlas.Sporadic.Conway2Simplicity
import Atlas.Sporadic.Conway2Generation
import Atlas
import Atlas.Lattices.IcosianRootNormShapes
import Atlas.Lattices.IcosianAxisRoots
import Atlas.Codes.IcosianDeterminantGlue
import Atlas.Algebra.IcosianNormTwoReductionFibers
import Atlas.Algebra.IcosianConjugation
import Atlas.Algebra.GoldenFourFinite
import Atlas.Lattices.IcosianEdgeRoots
import Atlas.Algebra.IcosianUnitNormFibers
import Atlas.Lattices.IcosianRootCDCounts
import Atlas.Conway.IcosianRootPointCount
import Atlas.Conway.IcosianFullFrameStabilizer
import Atlas.Conway.IcosianRootGeometryCard
/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ATLAS contributors
-/

/-! # Axiom dependencies of the principal exported results -/

#print axioms Atlas.gl_center_eq_scalars
#print axioms Atlas.gl_scalar_injective
#print axioms Atlas.card_gl_center
#print axioms Atlas.finite_pgl
#print axioms Atlas.card_pgl_mul
#print axioms Atlas.card_pgl
#print axioms Atlas.scalar_order_dvd_gl
#print axioms Atlas.card_gl
#print axioms Atlas.card_gl_factor
#print axioms Atlas.card_pgl_product
#print axioms Atlas.card_pgl_factor
#print axioms Atlas.card_projectiveSpace
#print axioms Atlas.card_projectiveSpace_sum
#print axioms Atlas.pgl_two_pretransitive
#print axioms Atlas.pgl_pretransitive
#print axioms Atlas.gl_mem_center_of_fixes_projectiveSpace
#print axioms Atlas.pgl_faithful

#print axioms Atlas.sl_mem_center_iff
#print axioms Atlas.sl_mem_center_iff_units
#print axioms Atlas.slCenterEquivPowerKernel
#print axioms Atlas.card_sl_center
#print axioms Atlas.psl_toPGL_injective
#print axioms Atlas.pglDet
#print axioms Atlas.pglDet_mk
#print axioms Atlas.pglDet_surjective
#print axioms Atlas.pglDet_ker
#print axioms Atlas.pslImage_normal
#print axioms Atlas.pglQuotientPSLEquiv
#print axioms Atlas.pglQuotientPSLEquiv_mk
#print axioms Atlas.index_pslImage
#print axioms Atlas.finite_psl
#print axioms Atlas.card_pslImage
#print axioms Atlas.card_psl_mul_pgl
#print axioms Atlas.diagonal_index_dvd_pgl
#print axioms Atlas.card_psl
#print axioms Atlas.card_psl_from_sl
#print axioms Atlas.card_psl_product
#print axioms Atlas.card_psl_factor
#print axioms Atlas.card_psl_mul_factors
#print axioms Atlas.psl_faithful
#print axioms Atlas.psl_two_pretransitive
#print axioms Atlas.psl_pretransitive
#print axioms Atlas.psl_primitive
#print axioms Atlas.psl_toPGL_smul
#print axioms Atlas.card_psl_two_two
#print axioms Atlas.card_psl_two_three
#print axioms Atlas.card_psl_two_four
#print axioms Atlas.card_psl_two_five
#print axioms Atlas.card_psl_three_two

#print axioms Atlas.elementary_mul
#print axioms Atlas.elementary_inv
#print axioms Atlas.elementary_det
#print axioms Atlas.diagonal_elementary_decomposition
#print axioms Atlas.sl_elementary_induction
#print axioms Atlas.sl_elementary_generation
#print axioms Atlas.psl_elementary_generation
#print axioms Atlas.elementary_commutator
#print axioms Atlas.sl_perfect
#print axioms Atlas.psl_perfect

/-! ## Simplicity, exceptions, and the type-A construction -/

#print axioms Atlas.lineTransvection
#print axioms Atlas.lineTransvection_apply
#print axioms Atlas.lineTransvection_mem
#print axioms Atlas.lineTransvection_mul
#print axioms Atlas.lineTransvection_zero
#print axioms Atlas.lineTransvection_inv
#print axioms Atlas.lineTransvection_det
#print axioms Atlas.lineTransvection_conjugate
#print axioms Atlas.lineTransvections_abelian
#print axioms Atlas.lineTransvections_fix_vectors
#print axioms Atlas.lineTransvections_intrinsic
#print axioms Atlas.lineTransvections_fix
#print axioms Atlas.lineTransvections_le_stabilizer
#print axioms Atlas.lineTransvections_conj
#print axioms Atlas.lineTransvections_normal
#print axioms Atlas.projectiveTransvections_abelian
#print axioms Atlas.projectiveTransvections_conj
#print axioms Atlas.projectiveTransvections_le_stabilizer
#print axioms Atlas.projectiveTransvections_normal
#print axioms Atlas.lineTransvections_generate
#print axioms Atlas.projectiveTransvections_generate
#print axioms Atlas.projectiveTransvections_conjugates_generate
#print axioms Atlas.pslIwasawa
#print axioms Atlas.psl_nontrivial
#print axioms Atlas.psl_simple_high_rank
#print axioms Atlas.psl_nonabelian_high_rank
#print axioms Atlas.psl_two_two_not_simple
#print axioms Atlas.psl_two_three_not_simple
#print axioms Atlas.psl_simple_rank_two
#print axioms Atlas.psl_nonabelian_rank_two
#print axioms Atlas.psl_simple_iff
#print axioms Atlas.psl_nonabelian_simple
#print axioms Atlas.typeA_construction
#print axioms Atlas.exists_typeA
#print axioms Atlas.typeA_prime_power
#print axioms Atlas.psl_two_two_check
#print axioms Atlas.psl_two_three_check
#print axioms Atlas.psl_two_four_check
#print axioms Atlas.psl_two_five_check
#print axioms Atlas.psl_three_two_check
#print axioms Atlas.psl_three_three_check

/-! ## Statement audit: all parameters, including implicit hypotheses -/

#check @Atlas.sl_elementary_generation
#check @Atlas.psl_elementary_generation
#check @Atlas.elementary_commutator
#check @Atlas.sl_perfect
#check @Atlas.psl_perfect
#check @Atlas.lineTransvections_intrinsic
#check @Atlas.lineTransvections_normal
#check @Atlas.projectiveTransvections_normal
#check @Atlas.projectiveTransvections_conjugates_generate
#check @Atlas.pslIwasawa
#check @Atlas.psl_nontrivial
#check @Atlas.psl_simple_high_rank
#check @Atlas.psl_nonabelian_high_rank
#check @Atlas.psl_two_two_not_simple
#check @Atlas.psl_two_three_not_simple
#check @Atlas.psl_simple_iff
#check @Atlas.psl_nonabelian_simple
#check @Atlas.typeA_construction
#check @Atlas.exists_typeA
#check @Atlas.typeA_prime_power

#print Atlas.TypeAConstruction

/-! ## Job 4: quadratic alphabets, trio, and additive hexacode -/

#print axioms Atlas.Codes.bit_two
#print axioms Atlas.Codes.bit_four
#print axioms Atlas.Codes.bit_five
#print axioms Atlas.Codes.bit_square
#print axioms Atlas.Codes.bit_self_add
#print axioms Atlas.Codes.oneL
#print axioms Atlas.Codes.spin
#print axioms Atlas.Codes.cospin
#print axioms Atlas.Codes.a
#print axioms Atlas.Codes.b
#print axioms Atlas.Codes.c
#print axioms Atlas.Codes.qL
#print axioms Atlas.Codes.qK
#print axioms Atlas.Codes.euclideanWeight
#print axioms Atlas.Codes.polar
#print axioms Atlas.Codes.polar_apply
#print axioms Atlas.Codes.qL_polar
#print axioms Atlas.Codes.qK_polar
#print axioms Atlas.Codes.euclideanWeight_mod_two
#print axioms Atlas.Codes.qK_eq_indicator
#print axioms Atlas.Codes.polar_symmetric
#print axioms Atlas.Codes.polar_nondegenerate
#print axioms Atlas.Codes.wordQ
#print axioms Atlas.Codes.wordPolar
#print axioms Atlas.Codes.wordPolar_apply
#print axioms Atlas.Codes.wordPolar_symmetric
#print axioms Atlas.Codes.wordPolar_nondegenerate
#print axioms Atlas.Codes.dual
#print axioms Atlas.Codes.wordQ_polar
#print axioms Atlas.Codes.wordQ_K_weight
#print axioms Atlas.Codes.selfDual_of_half_dimension
#print axioms Atlas.Codes.phi
#print axioms Atlas.Codes.phi_injective
#print axioms Atlas.Codes.phi_quadratic
#print axioms Atlas.Codes.phi_polar
#print axioms Atlas.Codes.phiWord
#print axioms Atlas.Codes.pairParityEncoder
#print axioms Atlas.Codes.equalPairs
#print axioms Atlas.Codes.eEncoder
#print axioms Atlas.Codes.eEncoder_apply
#print axioms Atlas.Codes.E0
#print axioms Atlas.Codes.tau
#print axioms Atlas.Codes.h0Encoder
#print axioms Atlas.Codes.H0
#print axioms Atlas.Codes.hexEncoder
#print axioms Atlas.Codes.hexacode
#print axioms Atlas.Codes.hexDecoder
#print axioms Atlas.Codes.hex_decode_encode
#print axioms Atlas.Codes.hexEncoder_injective
#print axioms Atlas.Codes.hexEquiv
#print axioms Atlas.Codes.h0Encoder_injective
#print axioms Atlas.Codes.eEncoder_injective
#print axioms Atlas.Codes.E0_finrank
#print axioms Atlas.Codes.H0_finrank
#print axioms Atlas.Codes.hexacode_finrank
#print axioms Atlas.Codes.hexacode_card
#print axioms Atlas.Codes.hexacode_isotropic
#print axioms Atlas.Codes.hexacode_selfDual
#print axioms Atlas.Codes.weight_le_of_zero_on_embedding
#print axioms Atlas.Codes.hexProjection
#print axioms Atlas.Codes.hexProjection_injective
#print axioms Atlas.Codes.hexProjection_bijective
#print axioms Atlas.Codes.hexCoordinate
#print axioms Atlas.Codes.hexCoordinate_surjective
#print axioms Atlas.Codes.hexCoordinate_fiber
#print axioms Atlas.Codes.hexWeightCount
#print axioms Atlas.Codes.hex_weights
#print axioms Atlas.Codes.hexWeightCount_zero
#print axioms Atlas.Codes.hex_weight_total
#print axioms Atlas.Codes.hexacode_weight_distribution
#print axioms Atlas.Codes.liftedPair
#print axioms Atlas.Codes.liftedPair_spin
#print axioms Atlas.Codes.liftedPair_cospin
#print axioms Atlas.Codes.liftedPair_one
#print axioms Atlas.Codes.liftedPair_zero
#print axioms Atlas.Codes.gluing_weight
#print axioms Atlas.Codes.nonzero_seed_weight
#print axioms Atlas.Codes.pairParityEncoder_even
#print axioms Atlas.Codes.equalPairs_weight
#print axioms Atlas.Codes.H0_minimum
#print axioms Atlas.Codes.odd_pair_nonzero
#print axioms Atlas.Codes.hexacode_minimum
#print axioms Atlas.Codes.hexacode_minimum_exact
#print axioms Atlas.Codes.pairParityEncoder_range
#print axioms Atlas.Codes.E0_description
#print axioms Atlas.Codes.eEquiv
#print axioms Atlas.Codes.h0Equiv
#print axioms Atlas.Codes.firstGluing
#print axioms Atlas.Codes.firstTwist
#print axioms Atlas.Codes.firstGluing_apply
#print axioms Atlas.Codes.firstTwist_apply
#print axioms Atlas.Codes.tau_not_mem_H0
#print axioms Atlas.Codes.hexacode_cosets
#print axioms Atlas.Codes.hexacode_cosets_disjoint
#print axioms Atlas.Codes.hexFlatParameters
#print axioms Atlas.Codes.hexBasis
#print axioms Atlas.Codes.hexGenerators
#print axioms Atlas.Codes.hexBasis_coe
#print axioms Atlas.Codes.hexGenerators_weight
#print axioms Atlas.Codes.hexGenerators_orthogonal
#print axioms Atlas.Codes.hexGenerators_isotropic
#print axioms Atlas.Codes.hexacode_even
#print axioms Atlas.Codes.trioEncoder
#print axioms Atlas.Codes.trio
#print axioms Atlas.Codes.trioEncoder_injective
#print axioms Atlas.Codes.trioEquiv
#print axioms Atlas.Codes.trioGenerators
#print axioms Atlas.Codes.trioEncoder_eq_sum
#print axioms Atlas.Codes.trio_generators_independent
#print axioms Atlas.Codes.trio_span
#print axioms Atlas.Codes.trioWords
#print axioms Atlas.Codes.trio_words
#print axioms Atlas.Codes.trio_finrank
#print axioms Atlas.Codes.trio_card
#print axioms Atlas.Codes.trio_isotropic
#print axioms Atlas.Codes.trio_selfDual
#print axioms Atlas.Codes.trioEuclideanWeight
#print axioms Atlas.Codes.trio_hamming_counts
#print axioms Atlas.Codes.trio_euclidean_counts
#print axioms Atlas.Codes.bit_cases
#print axioms Atlas.Codes.hammingNorm_prod
#print axioms Atlas.Codes.bit_sum_eq_weight
#print axioms Atlas.Codes.even_weight_iff
#print axioms Atlas.Codes.positive_even_weight
#print axioms Atlas.Codes.hammingNorm_eq_sum
#check @Atlas.Codes.trio_generators_independent
#check @Atlas.Codes.trio_words
#check @Atlas.Codes.trio_finrank
#check @Atlas.Codes.trio_card
#check @Atlas.Codes.trio_isotropic
#check @Atlas.Codes.trio_selfDual
#check @Atlas.Codes.trio_hamming_counts
#check @Atlas.Codes.trio_euclidean_counts
#check @Atlas.Codes.E0_description
#check @Atlas.Codes.firstGluing
#check @Atlas.Codes.firstGluing_apply
#check @Atlas.Codes.firstTwist
#check @Atlas.Codes.firstTwist_apply
#check @Atlas.Codes.hex_decode_encode
#check @Atlas.Codes.hexacode_cosets
#check @Atlas.Codes.hexacode_cosets_disjoint
#check @Atlas.Codes.hexacode_finrank
#check @Atlas.Codes.hexacode_card
#check @Atlas.Codes.hexBasis
#check @Atlas.Codes.hexBasis_coe
#check @Atlas.Codes.hexGenerators_weight
#check @Atlas.Codes.hexacode_selfDual
#check @Atlas.Codes.hexacode_minimum_exact
#check @Atlas.Codes.hexProjection_bijective
#check @Atlas.Codes.hexCoordinate_fiber
#check @Atlas.Codes.hexacode_weight_distribution

/-! ## Job 4: second twist and octad basis -/
#print axioms Atlas.Codes.parityEncoder
#print axioms Atlas.Codes.parityCode
#print axioms Atlas.Codes.parityEncoder_injective
#print axioms Atlas.Codes.parityEquiv
#print axioms Atlas.Codes.parityCode_mem
#print axioms Atlas.Codes.parityCode_finrank
#print axioms Atlas.Codes.parityCode_card
#print axioms Atlas.Codes.parityBasis
#print axioms Atlas.Codes.parityBasis_coe
#print axioms Atlas.Codes.hexIndexEquiv
#print axioms Atlas.Codes.binaryDot
#print axioms Atlas.Codes.binaryDot_apply
#print axioms Atlas.Codes.binaryDot_symmetric
#print axioms Atlas.Codes.binaryDot_nondegenerate
#print axioms Atlas.Codes.j
#print axioms Atlas.Codes.blockDecode
#print axioms Atlas.Codes.j_table
#print axioms Atlas.Codes.j_first
#print axioms Atlas.Codes.j_sum
#print axioms Atlas.Codes.j_dot
#print axioms Atlas.Codes.j_dot_ones
#print axioms Atlas.Codes.j_dot_first
#print axioms Atlas.Codes.blockDecode_j
#print axioms Atlas.Codes.blockDecode_constant
#print axioms Atlas.Codes.j_injective
#print axioms Atlas.Codes.jWord
#print axioms Atlas.Codes.rho
#print axioms Atlas.Codes.eta
#print axioms Atlas.Codes.eta_weight
#print axioms Atlas.Codes.eta_block_sum
#print axioms Atlas.Codes.eta_block_dot_j
#print axioms Atlas.Codes.R0
#print axioms Atlas.Codes.c0Encoder
#print axioms Atlas.Codes.C0
#print axioms Atlas.Codes.golayEncoder
#print axioms Atlas.Codes.golay
#print axioms Atlas.Codes.blockParity
#print axioms Atlas.Codes.golayEncoder_blockParity
#print axioms Atlas.Codes.support
#print axioms Atlas.Codes.overlap
#print axioms Atlas.Codes.overlap_eq_sum
#print axioms Atlas.Codes.binaryDot_overlap
#print axioms Atlas.Codes.binary_weight_add
#print axioms Atlas.Codes.doublyEven_add
#print axioms Atlas.Codes.j_weight
#print axioms Atlas.Codes.jWord_weight
#print axioms Atlas.Codes.rho_weight
#print axioms Atlas.Codes.c0Encoder_first
#print axioms Atlas.Codes.c0Encoder_decode
#print axioms Atlas.Codes.c0Encoder_injective
#print axioms Atlas.Codes.golayEncoder_injective
#print axioms Atlas.Codes.c0Equiv
#print axioms Atlas.Codes.golayEquiv
#print axioms Atlas.Codes.golayEquiv_apply
#print axioms Atlas.Codes.golayRawDecoder
#print axioms Atlas.Codes.golay_decode_encode
#print axioms Atlas.Codes.C0_finrank
#print axioms Atlas.Codes.golay_finrank
#print axioms Atlas.Codes.golay_card
#print axioms Atlas.Codes.C0_card
#print axioms Atlas.Codes.golay_cosets
#print axioms Atlas.Codes.eta_not_mem_C0
#print axioms Atlas.Codes.golay_cosets_disjoint
#print axioms Atlas.Codes.jWord_dot
#print axioms Atlas.Codes.jWord_rho_dot
#print axioms Atlas.Codes.rho_dot
#print axioms Atlas.Codes.eta_jWord_dot
#print axioms Atlas.Codes.eta_rho_dot
#print axioms Atlas.Codes.eta_dot_eta
#print axioms Atlas.Codes.c0Encoder_dot
#print axioms Atlas.Codes.eta_c0Encoder_dot
#print axioms Atlas.Codes.golay_selfOrthogonal
#print axioms Atlas.Codes.golay_selfDual
#print axioms Atlas.Codes.c0Encoder_doublyEven
#print axioms Atlas.Codes.golay_doublyEven
#print axioms Atlas.Codes.complemented_j_weight
#print axioms Atlas.Codes.c0Encoder_weight_bound
#print axioms Atlas.Codes.C0_minimum
#print axioms Atlas.Codes.golay_minimum
#print axioms Atlas.Codes.eta_mem_golay
#print axioms Atlas.Codes.golay_minimum_exact
#print axioms Atlas.Codes.golay_distance
#print axioms Atlas.Codes.golayFlatParameters
#print axioms Atlas.Codes.golayBasis
#print axioms Atlas.Codes.golayGenerators
#print axioms Atlas.Codes.golayBasis_coe
#print axioms Atlas.Codes.golayGenerators_weight
#print axioms Atlas.Codes.golay_octad_basis
#print axioms Atlas.Codes.octadWords
#print axioms Atlas.Codes.octads_span
#check @Atlas.Codes.parityCode_mem
#check @Atlas.Codes.j_table
#check @Atlas.Codes.j_dot
#check @Atlas.Codes.j_dot_ones
#check @Atlas.Codes.j_dot_first
#check @Atlas.Codes.golayEquiv
#check @Atlas.Codes.golayEquiv_apply
#check @Atlas.Codes.golay_decode_encode
#check @Atlas.Codes.golay_cosets
#check @Atlas.Codes.golay_cosets_disjoint
#check @Atlas.Codes.C0_finrank
#check @Atlas.Codes.golay_finrank
#check @Atlas.Codes.golay_card
#check @Atlas.Codes.golay_selfDual
#check @Atlas.Codes.golay_doublyEven
#check @Atlas.Codes.golay_minimum_exact
#check @Atlas.Codes.golay_distance
#check @Atlas.Codes.golay_octad_basis
#check @Atlas.Codes.octads_span

/-! ## Job 4: counts, Witt design, markings, recovery, and automorphisms -/
#print axioms Atlas.Codes.qL_homogeneous
#print axioms Atlas.Codes.qK_homogeneous
#print axioms Atlas.Codes.binarySupportEquiv
#print axioms Atlas.Codes.binary_weight_count
#print axioms Atlas.Codes.parityFiberEquiv
#print axioms Atlas.Codes.parity_weight_count
#print axioms Atlas.Codes.oddParityTranslation
#print axioms Atlas.Codes.odd_parity_weight_count
#print axioms Atlas.Codes.overlap_inter
#print axioms Atlas.Codes.middleWeights
#print axioms Atlas.Codes.evenCosetCount
#print axioms Atlas.Codes.oddCosetCount
#print axioms Atlas.Codes.golayWeightCount
#print axioms Atlas.Codes.card_subtype_prod_sum
#print axioms Atlas.Codes.evenCosetCount_sum
#print axioms Atlas.Codes.oddCosetCount_sum
#print axioms Atlas.Codes.even_slice_zero
#print axioms Atlas.Codes.even_slice_four
#print axioms Atlas.Codes.even_slice_six
#print axioms Atlas.Codes.even_middle_counts
#print axioms Atlas.Codes.odd_middle_counts
#print axioms Atlas.Codes.golayWeightCount_cosets
#print axioms Atlas.Codes.golay_middle_counts
#print axioms Atlas.Codes.allOnes
#print axioms Atlas.Codes.allOnes_mem_C0
#print axioms Atlas.Codes.C0_le_golay
#print axioms Atlas.Codes.complement_weight
#print axioms Atlas.Codes.golay_weights
#print axioms Atlas.Codes.weight_twentyfour_iff
#print axioms Atlas.Codes.code_extreme_count
#print axioms Atlas.Codes.golay_weight_distribution
#print axioms Atlas.Codes.even_coset_distribution
#print axioms Atlas.Codes.odd_coset_distribution
#print axioms Atlas.Codes.hammingNorm_equiv
#print axioms Atlas.Codes.zeroPositions
#print axioms Atlas.Codes.zeroPositions_card
#print axioms Atlas.Codes.zeroPositions_embedding
#print axioms Atlas.Codes.c0Encoder_weight_formula
#print axioms Atlas.Codes.c0_weight_four
#print axioms Atlas.Codes.c0_weight_four_count
#print axioms Atlas.Codes.c0_weight_six
#print axioms Atlas.Codes.c0_weight_zero_count
#print axioms Atlas.Codes.tetradEmbedding
#print axioms Atlas.Codes.tetrad
#print axioms Atlas.Codes.mem_tetrad
#print axioms Atlas.Codes.tetrad_card
#print axioms Atlas.Codes.tetrads_partition
#print axioms Atlas.Codes.tetrads_disjoint
#print axioms Atlas.Codes.tetrad_pair_octad
#print axioms Atlas.Codes.distinguished_sextet
#print axioms Atlas.Codes.distinguishedTrio
#print axioms Atlas.Codes.distinguishedTrio_octads
#print axioms Atlas.Codes.distinguishedTrio_compatibility
#print axioms Atlas.Codes.distinguishedTrio_partition
#print axioms Atlas.Codes.letterPair
#print axioms Atlas.Codes.letterPair_table
#print axioms Atlas.Codes.letterPair_card
#print axioms Atlas.Codes.letterPair_partition
#print axioms Atlas.Codes.distinguishedMarking
#print axioms Atlas.Codes.markedPair
#print axioms Atlas.Codes.markedPair_card
#print axioms Atlas.Codes.markedPair_mem
#print axioms Atlas.Codes.markedPair_subset_tetrad
#print axioms Atlas.Codes.markedPairs_partition
#print axioms Atlas.Codes.oddMask
#print axioms Atlas.Codes.oddMask_parity
#print axioms Atlas.Codes.odd_block_weight
#print axioms Atlas.Codes.odd_word_weight
#print axioms Atlas.Codes.oddWordEquiv
#print axioms Atlas.Codes.odd_word_count
#print axioms Atlas.Codes.odd_word_counts
#print axioms Atlas.Codes.golay_from_trio
#print axioms Atlas.Codes.exists_golay_from_trio
#print axioms Atlas.Codes.even_block_decomposition
#print axioms Atlas.Codes.C0_even_blocks
#print axioms Atlas.Codes.recoverHex
#print axioms Atlas.Codes.recoverHex_apply
#print axioms Atlas.Codes.recoverHex_blocks
#print axioms Atlas.Codes.recoverHex_surjective
#print axioms Atlas.Codes.recoverHex_kernel
#print axioms Atlas.Codes.recoverTrio
#print axioms Atlas.Codes.recoverTrio_apply
#print axioms Atlas.Codes.recoverTrio_surjective
#print axioms Atlas.Codes.recoverTrio_kernel
#print axioms Atlas.Codes.phiWord_injective
#print axioms Atlas.Codes.phiWord_quadratic
#print axioms Atlas.Codes.phiWord_polar
#print axioms Atlas.Codes.parityProjection
#print axioms Atlas.Codes.parityProjection_surjective
#print axioms Atlas.Codes.parityProjection_fiber
#print axioms Atlas.Codes.parityProjection_weight_count
#print axioms Atlas.Codes.hexEnumerator
#print axioms Atlas.Codes.golayEnumerator
#print axioms Atlas.Codes.evenCosetEnumerator
#print axioms Atlas.Codes.oddCosetEnumerator
#print axioms Atlas.Codes.hexEnumerator_coeff
#print axioms Atlas.Codes.golayEnumerator_coeff
#print axioms Atlas.Codes.evenCosetEnumerator_coeff
#print axioms Atlas.Codes.oddCosetEnumerator_coeff
#print axioms Atlas.Codes.hexEnumerator_eq
#print axioms Atlas.Codes.golayEnumerator_eq
#print axioms Atlas.Codes.evenCosetEnumerator_eq
#print axioms Atlas.Codes.oddCosetEnumerator_eq
#print axioms Atlas.Codes.golay_homogeneous_enumerator
#print axioms Atlas.Codes.octads
#print axioms Atlas.Codes.support_injective
#print axioms Atlas.Codes.octads_mem
#print axioms Atlas.Codes.octads_card
#print axioms Atlas.Codes.octad_size
#print axioms Atlas.Codes.octad_unique_on_five
#print axioms Atlas.Codes.incidenceProjection
#print axioms Atlas.Codes.incidenceProjection_injective
#print axioms Atlas.Codes.incidenceProjection_bijective
#print axioms Atlas.Codes.octad_steiner
#print axioms Atlas.Codes.coordinatePermutation
#print axioms Atlas.Codes.coordinatePermutation_one
#print axioms Atlas.Codes.coordinatePermutation_mul
#print axioms Atlas.Codes.coordinatePermutation_weight
#print axioms Atlas.Codes.permuteBlock
#print axioms Atlas.Codes.permuteBlock_one
#print axioms Atlas.Codes.permuteBlock_mul
#print axioms Atlas.Codes.coordinatePermutation_support
#print axioms Atlas.Codes.CodePreserving
#print axioms Atlas.Codes.OctadPreserving
#print axioms Atlas.Codes.codeAutomorphisms
#print axioms Atlas.Codes.octadAutomorphisms
#print axioms Atlas.Codes.codePreserving_octad_forward
#print axioms Atlas.Codes.codePreserving_octadPreserving
#print axioms Atlas.Codes.octadPreserving_code_forward
#print axioms Atlas.Codes.octadPreserving_codePreserving
#print axioms Atlas.Codes.codeAutomorphisms_eq_octadAutomorphisms
#print axioms Atlas.Codes.codeAutomorphisms_finite
#print axioms Atlas.Codes.codeAutomorphisms_faithful
#check @Atlas.Codes.qL_homogeneous
#check @Atlas.Codes.qK_homogeneous
#check @Atlas.Codes.phiWord_injective
#check @Atlas.Codes.phiWord_quadratic
#check @Atlas.Codes.phiWord_polar
#check @Atlas.Codes.binary_weight_count
#check @Atlas.Codes.parity_weight_count
#check @Atlas.Codes.parityProjection_fiber
#check @Atlas.Codes.odd_word_count
#check @Atlas.Codes.c0_weight_four_count
#check @Atlas.Codes.even_coset_distribution
#check @Atlas.Codes.odd_coset_distribution
#check @Atlas.Codes.golay_weight_distribution
#check @Atlas.Codes.golay_homogeneous_enumerator
#check @Atlas.Codes.octads_card
#check @Atlas.Codes.octad_unique_on_five
#check @Atlas.Codes.incidenceProjection_bijective
#check @Atlas.Codes.octad_steiner
#check @Atlas.Codes.distinguished_sextet
#check @Atlas.Codes.distinguishedTrio_octads
#check @Atlas.Codes.distinguishedTrio_partition
#check @Atlas.Codes.distinguishedTrio_compatibility
#check @Atlas.Codes.letterPair_table
#check @Atlas.Codes.markedPairs_partition
#check @Atlas.Codes.markedPair_subset_tetrad
#check @Atlas.Codes.even_block_decomposition
#check @Atlas.Codes.C0_even_blocks
#check @Atlas.Codes.recoverHex_surjective
#check @Atlas.Codes.recoverHex_kernel
#check @Atlas.Codes.recoverHex_blocks
#check @Atlas.Codes.recoverTrio_surjective
#check @Atlas.Codes.recoverTrio_kernel
#check @Atlas.Codes.codeAutomorphisms_eq_octadAutomorphisms
#check @Atlas.Codes.codeAutomorphisms_finite
#check @Atlas.Codes.codeAutomorphisms_faithful
#check @Atlas.Codes.golay_from_trio
#check @Atlas.Codes.exists_golay_from_trio

#print Atlas.Codes.GolayFromTrio
#print Atlas.Codes.IsSextet
#print Atlas.Codes.CodePreserving
#print Atlas.Codes.OctadPreserving

/-! Job 5: Checkpoint HA, the full additive monomial automorphism group. -/
#print axioms Atlas.Codes.KIsometry
#print axioms Atlas.Codes.k_inv_apply_apply
#print axioms Atlas.Codes.k_apply_inv_apply
#print axioms Atlas.Codes.KIsometry.map_q
#print axioms Atlas.Codes.KIsometry.map_polar
#print axioms Atlas.Codes.kAlphabetEquiv
#print axioms Atlas.Codes.kAlphabetMulEquiv
#print axioms Atlas.Codes.NonzeroK
#print axioms Atlas.Codes.kNonzeroPerm
#print axioms Atlas.Codes.letter_add_characterization
#print axioms Atlas.Codes.zeroFixing_add
#print axioms Atlas.Codes.zeroFixingLinear
#print axioms Atlas.Codes.extendNonzero
#print axioms Atlas.Codes.kNonzeroPerm_bijective
#print axioms Atlas.Codes.kIsometryPermEquiv
#print axioms Atlas.Codes.nonzeroK_card
#print axioms Atlas.Codes.kIsometry_card
#print axioms Atlas.Codes.localU
#print axioms Atlas.Codes.localV
#print axioms Atlas.Codes.localW
#print axioms Atlas.Codes.localKappa
#print axioms Atlas.Codes.localU_apply
#print axioms Atlas.Codes.localV_apply
#print axioms Atlas.Codes.localW_apply
#print axioms Atlas.Codes.localKappa_apply
#print axioms Atlas.Codes.localU_sq
#print axioms Atlas.Codes.localV_sq
#print axioms Atlas.Codes.localW_sq
#print axioms Atlas.Codes.localKappa_cube
#print axioms Atlas.Codes.localKappa_inv_apply
#print axioms Atlas.Codes.local_maps_table
#print axioms Atlas.Codes.kIsometry_ext_ab
#print axioms Atlas.Codes.nonzero_distinct_pairs
#print axioms Atlas.Codes.kIsometry_eq_six
#print axioms Atlas.Codes.kIsometry_centralizer
#print axioms Atlas.Codes.Monomial
#print axioms Atlas.Codes.Monomial.one_perm
#print axioms Atlas.Codes.Monomial.one_local
#print axioms Atlas.Codes.Monomial.mul_perm
#print axioms Atlas.Codes.Monomial.mul_local
#print axioms Atlas.Codes.Monomial.inv_perm
#print axioms Atlas.Codes.Monomial.inv_local
#print axioms Atlas.Codes.Monomial.coordinateHom
#print axioms Atlas.Codes.Monomial.act
#print axioms Atlas.Codes.Monomial.act_apply
#print axioms Atlas.Codes.Monomial.act_one
#print axioms Atlas.Codes.Monomial.act_mul
#print axioms Atlas.Codes.Monomial.linearHom
#print axioms Atlas.Codes.Monomial.act_weight
#print axioms Atlas.Codes.Monomial.act_quadratic
#print axioms Atlas.Codes.Monomial.act_polar
#print axioms Atlas.Codes.Monomial.stabilizer
#print axioms Atlas.Codes.Monomial.restriction
#print axioms Atlas.Codes.hexPos
#print axioms Atlas.Codes.hexPos_order
#print axioms Atlas.Codes.hexPos_index
#print axioms Atlas.Codes.index_hexPos
#print axioms Atlas.Codes.firstThree
#print axioms Atlas.Codes.systematicEncoder
#print axioms Atlas.Codes.systematic_pos0
#print axioms Atlas.Codes.systematic_pos1
#print axioms Atlas.Codes.systematic_pos2
#print axioms Atlas.Codes.systematic_pos3
#print axioms Atlas.Codes.systematic_pos4
#print axioms Atlas.Codes.systematic_pos5
#print axioms Atlas.Codes.systematic_on_basis
#print axioms Atlas.Codes.systematic_reconstruct
#print axioms Atlas.Codes.systematic_mem
#print axioms Atlas.Codes.hexacode_systematic
#print axioms Atlas.Codes.HexAutomorphisms
#print axioms Atlas.Codes.hexCoordinateHom
#print axioms Atlas.Codes.hexAction
#print axioms Atlas.Codes.monomial_mem_of_hexBasis
#print axioms Atlas.Codes.hexZRaw
#print axioms Atlas.Codes.hexLiftLocals
#print axioms Atlas.Codes.hexLiftRaw
#print axioms Atlas.Codes.hexZRaw_preserves_basis
#print axioms Atlas.Codes.hexLiftRaw_preserves_basis
#print axioms Atlas.Codes.hexZ
#print axioms Atlas.Codes.hexLift
#print axioms Atlas.Codes.hexZ_coordinate
#print axioms Atlas.Codes.hexLift_coordinate
#print axioms Atlas.Codes.hexZ_cube
#print axioms Atlas.Codes.hexZ_ne_one
#print axioms Atlas.Codes.hexLift_sq
#print axioms Atlas.Codes.hexLift_inverts
#print axioms Atlas.Codes.hex_kernel_relations
#print axioms Atlas.Codes.hex_kernel_trichotomy
#print axioms Atlas.Codes.hex_kernel_iff
#print axioms Atlas.Codes.hexCoordinateSixHom
#print axioms Atlas.Codes.hexSix_eq_one
#print axioms Atlas.Codes.hexLift_six
#print axioms Atlas.Codes.hexZ_six
#print axioms Atlas.Codes.adjacent_closure
#print axioms Atlas.Codes.hexCoordinateSix_surjective
#print axioms Atlas.Codes.hexCoordinateHom_surjective
#print axioms Atlas.Codes.hexZ_order
#print axioms Atlas.Codes.hexCoordinate_kernel
#print axioms Atlas.Codes.hexCoordinateSix_kernel
#print axioms Atlas.Codes.hex_kernel_card
#print axioms Atlas.Codes.hexAutomorphisms_card
#print axioms Atlas.Codes.hexGeneratingSet
#print axioms Atlas.Codes.hexAutomorphisms_generated
#print axioms Atlas.Codes.hex_two_values
#print axioms Atlas.Codes.hexAction_eq_one
#print axioms Atlas.Codes.hexAction_injective
#print axioms Atlas.Codes.hexSign
#print axioms Atlas.Codes.hexSign_Z
#print axioms Atlas.Codes.hexSign_lift
#print axioms Atlas.Codes.hex_conjugation_zpow
#print axioms Atlas.Codes.hex_conjugation_even
#print axioms Atlas.Codes.hex_conjugation_odd
#print axioms Atlas.Codes.HexEvenAutomorphisms
#print axioms Atlas.Codes.hexEvenCoordinate
#print axioms Atlas.Codes.hexEvenCoordinate_surjective
#print axioms Atlas.Codes.hex_even_kernel_central
#print axioms Atlas.Codes.hexX
#print axioms Atlas.Codes.hexY
#print axioms Atlas.Codes.hexX_coordinate
#print axioms Atlas.Codes.hexY_coordinate
#print axioms Atlas.Codes.hexX_even
#print axioms Atlas.Codes.hexY_even
#print axioms Atlas.Codes.hexXY_coordinate_commute
#print axioms Atlas.Codes.hexXY_commutator
#print axioms Atlas.Codes.hexZ_square_ne_one
#print axioms Atlas.Codes.hexXY_not_commute
#print axioms Atlas.Codes.hexXY_lifts_not_commute
#print axioms Atlas.Codes.hexEven_no_section
#print axioms Atlas.Codes.hex_no_section
#print axioms Atlas.Codes.hexSign_surjective
#print axioms Atlas.Codes.hexEven_card
#print axioms Atlas.Codes.hexEvenZ
#print axioms Atlas.Codes.hexEvenZ_order
#print axioms Atlas.Codes.hexEvenCoordinate_kernel
#print axioms Atlas.Codes.hexEven_kernel_card
#print axioms Atlas.Codes.HexacodeAutomorphismPackage
#print axioms Atlas.Codes.hexacode_automorphism_package

set_option pp.universes true in
#check @Atlas.Codes.hexacode_systematic
#check @Atlas.Codes.hexAction_injective
#check @Atlas.Codes.hexCoordinateSix_surjective
#check @Atlas.Codes.hex_kernel_iff
#check @Atlas.Codes.hexCoordinate_kernel
#check @Atlas.Codes.hexZ_order
#check @Atlas.Codes.hexAutomorphisms_generated
#check @Atlas.Codes.hexAutomorphisms_card
#check @Atlas.Codes.hex_conjugation_even
#check @Atlas.Codes.hex_conjugation_odd
#check @Atlas.Codes.hexEven_card
#check @Atlas.Codes.hexEvenCoordinate_kernel
#check @Atlas.Codes.hexXY_commutator
#check @Atlas.Codes.hexXY_lifts_not_commute
#check @Atlas.Codes.hexEven_no_section
#check @Atlas.Codes.hex_no_section
#check @Atlas.Codes.hexacode_automorphism_package
#print Atlas.Codes.Monomial
#print Atlas.Codes.Monomial.stabilizer
#print Atlas.Codes.hexCoordinateHom
#print Atlas.Codes.hexCoordinateSixHom
#print Atlas.Codes.HexAutomorphisms
#print Atlas.Codes.HexEvenAutomorphisms
#print Atlas.Codes.hexSign
#print Atlas.Codes.hexGeneratingSet
#print Atlas.Codes.HexacodeAutomorphismPackage

/-! Job 5: Checkpoint SG, all unordered sextets. -/
#print axioms Atlas.Codes.IsUnorderedSextet
#print axioms Atlas.Codes.UnorderedSextet
#print axioms Atlas.Codes.FourSet
#print axioms Atlas.Codes.IsUnorderedSextet.parts_disjoint
#print axioms Atlas.Codes.IsSextet.injective
#print axioms Atlas.Codes.labelledSextetParts
#print axioms Atlas.Codes.labelledSextetParts_valid
#print axioms Atlas.Codes.distinguishedUnorderedSextet
#print axioms Atlas.Codes.sextetLabelling
#print axioms Atlas.Codes.labelSextet
#print axioms Atlas.Codes.labelSextet_parts
#print axioms Atlas.Codes.labelSextet_valid
#print axioms Atlas.Codes.unordered_labelled_bridge
#print axioms Atlas.Codes.labelledSextetParts_relabel
#print axioms Atlas.Codes.tetradCompanions
#print axioms Atlas.Codes.companion_mem
#print axioms Atlas.Codes.companion_card
#print axioms Atlas.Codes.companion_disjoint
#print axioms Atlas.Codes.companion_union_octad
#print axioms Atlas.Codes.companion_unique_at_point
#print axioms Atlas.Codes.companion_covers
#print axioms Atlas.Codes.sextetCompletionParts
#print axioms Atlas.Codes.completion_part_card
#print axioms Atlas.Codes.completion_partition
#print axioms Atlas.Codes.completion_six_parts
#print axioms Atlas.Codes.companion_count
#print axioms Atlas.Codes.support_add_sdiff
#print axioms Atlas.Codes.octad_union_from_common_tetrad
#print axioms Atlas.Codes.companions_pair_octad
#print axioms Atlas.Codes.completion_valid
#print axioms Atlas.Codes.sextetCompletion
#print axioms Atlas.Codes.tetrad_mem_completion
#print axioms Atlas.Codes.sextet_eq_completion
#print axioms Atlas.Codes.unique_sextet_through_tetrad
#print axioms Atlas.Codes.completion_eq_iff
#print axioms Atlas.Codes.SextetIncidence
#print axioms Atlas.Codes.sextetIncidenceProjection
#print axioms Atlas.Codes.sextetIncidenceProjection_bijective
#print axioms Atlas.Codes.sextetIncidenceEquiv
#print axioms Atlas.Codes.sextet_incidence_count
#print axioms Atlas.Codes.unordered_sextets_card
#print axioms Atlas.Codes.completionFiberEquiv
#print axioms Atlas.Codes.completion_fiber_card
#print axioms Atlas.Codes.permuteBlock_injective
#print axioms Atlas.Codes.permuteBlock_card
#print axioms Atlas.Codes.permuteSextetParts
#print axioms Atlas.Codes.permuteSextetParts_one
#print axioms Atlas.Codes.permuteSextetParts_mul
#print axioms Atlas.Codes.permuteSextetParts_valid
#print axioms Atlas.Codes.sextetAction
#print axioms Atlas.Codes.sextetAction_one
#print axioms Atlas.Codes.sextetAction_mul
#print axioms Atlas.Codes.permuteFourSet
#print axioms Atlas.Codes.sextetCompletion_equivariant
#print axioms Atlas.Codes.SextetGeometryPackage
#print axioms Atlas.Codes.sextet_geometry_package
#check @Atlas.Codes.unordered_labelled_bridge
#check @Atlas.Codes.labelledSextetParts_relabel
#check @Atlas.Codes.companion_count
#check @Atlas.Codes.completion_valid
#check @Atlas.Codes.unique_sextet_through_tetrad
#check @Atlas.Codes.completion_fiber_card
#check @Atlas.Codes.sextet_incidence_count
#check @Atlas.Codes.unordered_sextets_card
#check @Atlas.Codes.sextetCompletion_equivariant
#check @Atlas.Codes.sextet_geometry_package
#print Atlas.Codes.IsUnorderedSextet
#print Atlas.Codes.UnorderedSextet
#print Atlas.Codes.FourSet
#print Atlas.Codes.tetradCompanions
#print Atlas.Codes.sextetCompletionParts
#print Atlas.Codes.sextetCompletion
#print Atlas.Codes.sextetAction
#print Atlas.Codes.SextetGeometryPackage

/-! # Job 5: full sextet stabilizer and final package -/
#print axioms Atlas.Codes.codePreserving_of_forward
#check @Atlas.Codes.codePreserving_of_forward
#print axioms Atlas.Codes.affineRepetition_sum
#check @Atlas.Codes.affineRepetition_sum
#print axioms Atlas.Codes.hexacode_orthogonal
#check @Atlas.Codes.hexacode_orthogonal
#print axioms Atlas.Codes.affine_preserves_code
#check @Atlas.Codes.affine_preserves_code
#print axioms Atlas.Codes.rowEncoder_eta
#check @Atlas.Codes.rowEncoder_eta
#print axioms Atlas.Codes.affine_preservation_necessary
#check @Atlas.Codes.affine_preservation_necessary
#print axioms Atlas.Codes.affine_code_preservation_iff
#check @Atlas.Codes.affine_code_preservation_iff
#print axioms Atlas.Codes.letter_neg
#check @Atlas.Codes.letter_neg
#print axioms Atlas.Codes.qK_add
#check @Atlas.Codes.qK_add
#print axioms Atlas.Codes.polar_isometry_inv
#check @Atlas.Codes.polar_isometry_inv
#print axioms Atlas.Codes.affineRepetition
#print Atlas.Codes.affineRepetition
#print axioms Atlas.Codes.affine_encoder_transform
#check @Atlas.Codes.affine_encoder_transform
#print axioms Atlas.Codes.affinePermutation
#print Atlas.Codes.affinePermutation
#print axioms Atlas.Codes.affinePermutation_apply
#check @Atlas.Codes.affinePermutation_apply
#print axioms Atlas.Codes.affinePermutation_inv_apply
#check @Atlas.Codes.affinePermutation_inv_apply
#print axioms Atlas.Codes.affinePermutation_zero_one
#check @Atlas.Codes.affinePermutation_zero_one
#print axioms Atlas.Codes.affinePermutation_mul
#check @Atlas.Codes.affinePermutation_mul
#print axioms Atlas.Codes.affinePermutation_injective
#check @Atlas.Codes.affinePermutation_injective
#print axioms Atlas.Codes.affinePermutation_tetrad
#check @Atlas.Codes.affinePermutation_tetrad
#print axioms Atlas.Codes.affinePermutation_preserves_parts
#check @Atlas.Codes.affinePermutation_preserves_parts
#print axioms Atlas.Codes.planeLinearAction
#print Atlas.Codes.planeLinearAction
#print axioms Atlas.Codes.AffinePlaneGroup
#print Atlas.Codes.AffinePlaneGroup
#print axioms Atlas.Codes.affinePlaneHom
#print Atlas.Codes.affinePlaneHom
#print axioms Atlas.Codes.affinePlaneHom_apply
#check @Atlas.Codes.affinePlaneHom_apply
#print axioms Atlas.Codes.affinePlaneHom_bijective
#check @Atlas.Codes.affinePlaneHom_bijective
#print axioms Atlas.Codes.affinePlaneEquiv
#print Atlas.Codes.affinePlaneEquiv
#print axioms Atlas.Codes.rowLabel
#print Atlas.Codes.rowLabel
#print axioms Atlas.Codes.rowLabel_table
#check @Atlas.Codes.rowLabel_table
#print axioms Atlas.Codes.letter_self_add
#check @Atlas.Codes.letter_self_add
#print axioms Atlas.Codes.j_row_polar
#check @Atlas.Codes.j_row_polar
#print axioms Atlas.Codes.lastColumnBit
#print Atlas.Codes.lastColumnBit
#print axioms Atlas.Codes.eta_row_quadratic
#check @Atlas.Codes.eta_row_quadratic
#print axioms Atlas.Codes.rowLinearPart
#print Atlas.Codes.rowLinearPart
#print axioms Atlas.Codes.row_affine_formula
#check @Atlas.Codes.row_affine_formula
#print axioms Atlas.Codes.row_affine_unique
#check @Atlas.Codes.row_affine_unique
#print axioms Atlas.Codes.rowEncoder
#print Atlas.Codes.rowEncoder
#print axioms Atlas.Codes.rowEncoder_lift
#check @Atlas.Codes.rowEncoder_lift
#print axioms Atlas.Codes.rowEncoder_golayEquiv
#check @Atlas.Codes.rowEncoder_golayEquiv
#print axioms Atlas.Codes.affine_block_parity
#check @Atlas.Codes.affine_block_parity
#print axioms Atlas.Codes.rowEncoder_blockParity
#check @Atlas.Codes.rowEncoder_blockParity
#print axioms Atlas.Codes.affine_linear_block_decode
#check @Atlas.Codes.affine_linear_block_decode
#print axioms Atlas.Codes.rowEncoder_decode
#check @Atlas.Codes.rowEncoder_decode
#print axioms Atlas.Codes.rowEncoder_injective
#check @Atlas.Codes.rowEncoder_injective
#print axioms Atlas.Codes.rowEncoder_mem_iff
#check @Atlas.Codes.rowEncoder_mem_iff
#print axioms Atlas.Codes.HexacodeSextetPackage
#print Atlas.Codes.HexacodeSextetPackage
#print axioms Atlas.Codes.hexacode_sextet_package
#check @Atlas.Codes.hexacode_sextet_package
#print axioms Atlas.Codes.PreservesTetradPartition
#print Atlas.Codes.PreservesTetradPartition
#print axioms Atlas.Codes.partition_image_tetrad
#check @Atlas.Codes.partition_image_tetrad
#print axioms Atlas.Codes.partitionColumn
#print Atlas.Codes.partitionColumn
#print axioms Atlas.Codes.partitionRow
#print Atlas.Codes.partitionRow
#print axioms Atlas.Codes.partition_first_coordinate
#check @Atlas.Codes.partition_first_coordinate
#print axioms Atlas.Codes.partitionRow_injective
#check @Atlas.Codes.partitionRow_injective
#print axioms Atlas.Codes.partitionRowEquiv
#print Atlas.Codes.partitionRowEquiv
#print axioms Atlas.Codes.partitionColumn_injective
#check @Atlas.Codes.partitionColumn_injective
#print axioms Atlas.Codes.partitionColumnEquiv
#print Atlas.Codes.partitionColumnEquiv
#print axioms Atlas.Codes.partitionRowLabels
#print Atlas.Codes.partitionRowLabels
#print axioms Atlas.Codes.partitionRowLabels_apply
#check @Atlas.Codes.partitionRowLabels_apply
#print axioms Atlas.Codes.partitionTranslation
#print Atlas.Codes.partitionTranslation
#print axioms Atlas.Codes.partitionMonomial
#print Atlas.Codes.partitionMonomial
#print axioms Atlas.Codes.partition_affine_reconstruction
#check @Atlas.Codes.partition_affine_reconstruction
#print axioms Atlas.Codes.partition_affine_unique
#check @Atlas.Codes.partition_affine_unique
#print axioms Atlas.Codes.transformedMarking
#print Atlas.Codes.transformedMarking
#print axioms Atlas.Codes.markingHalfSwap
#print Atlas.Codes.markingHalfSwap
#print axioms Atlas.Codes.markingHalfSwap_test
#check @Atlas.Codes.markingHalfSwap_test
#print axioms Atlas.Codes.affine_letterPair
#check @Atlas.Codes.affine_letterPair
#print axioms Atlas.Codes.affine_markedPair
#check @Atlas.Codes.affine_markedPair
#print axioms Atlas.Codes.sextet_marking_compatibility
#check @Atlas.Codes.sextet_marking_compatibility
#print axioms Atlas.Codes.rowEncoder_C0
#check @Atlas.Codes.rowEncoder_C0
#print axioms Atlas.Codes.rowEncoder_zero_mem_C0
#check @Atlas.Codes.rowEncoder_zero_mem_C0
#print axioms Atlas.Codes.recoverHex_rowEncoder
#check @Atlas.Codes.recoverHex_rowEncoder
#print axioms Atlas.Codes.affine_preserves_C0
#check @Atlas.Codes.affine_preserves_C0
#print axioms Atlas.Codes.sextet_preserves_C0
#check @Atlas.Codes.sextet_preserves_C0
#print axioms Atlas.Codes.sextetC0Action
#print Atlas.Codes.sextetC0Action
#print axioms Atlas.Codes.recoverHex_equivariant
#check @Atlas.Codes.recoverHex_equivariant
#print axioms Atlas.Codes.sextet_preserves_R0
#check @Atlas.Codes.sextet_preserves_R0
#print axioms Atlas.Codes.sextet_translation_trivial_recovery
#check @Atlas.Codes.sextet_translation_trivial_recovery
#print axioms Atlas.Codes.sextet_coordinate_compatibility
#check @Atlas.Codes.sextet_coordinate_compatibility
#print axioms Atlas.Codes.sextetTranslation
#print Atlas.Codes.sextetTranslation
#print axioms Atlas.Codes.sextetSection
#print Atlas.Codes.sextetSection
#print axioms Atlas.Codes.sextetQuotient
#print Atlas.Codes.sextetQuotient
#print axioms Atlas.Codes.sextetQuotient_affine
#check @Atlas.Codes.sextetQuotient_affine
#print axioms Atlas.Codes.sextetQuotient_section
#check @Atlas.Codes.sextetQuotient_section
#print axioms Atlas.Codes.sextetQuotient_translation
#check @Atlas.Codes.sextetQuotient_translation
#print axioms Atlas.Codes.sextet_section_splits
#check @Atlas.Codes.sextet_section_splits
#print axioms Atlas.Codes.sextetQuotient_surjective
#check @Atlas.Codes.sextetQuotient_surjective
#print axioms Atlas.Codes.sextetTranslation_injective
#check @Atlas.Codes.sextetTranslation_injective
#print axioms Atlas.Codes.sextetTranslation_coordinates
#check @Atlas.Codes.sextetTranslation_coordinates
#print axioms Atlas.Codes.sextetSection_coordinates
#check @Atlas.Codes.sextetSection_coordinates
#print axioms Atlas.Codes.sextet_translation_conjugation
#check @Atlas.Codes.sextet_translation_conjugation
#print axioms Atlas.Codes.sextetQuotient_kernel
#check @Atlas.Codes.sextetQuotient_kernel
#print axioms Atlas.Codes.sextetQuotient_kernel_card
#check @Atlas.Codes.sextetQuotient_kernel_card
#print axioms Atlas.Codes.sextetCoordinateHom
#print Atlas.Codes.sextetCoordinateHom
#print axioms Atlas.Codes.hexKernelAffineAction
#print Atlas.Codes.hexKernelAffineAction
#print axioms Atlas.Codes.SextetColumnKernelAffine
#print Atlas.Codes.SextetColumnKernelAffine
#print axioms Atlas.Codes.columnKernelInclusion
#print Atlas.Codes.columnKernelInclusion
#print axioms Atlas.Codes.columnKernelHom
#print Atlas.Codes.columnKernelHom
#print axioms Atlas.Codes.columnKernelHom_bijective
#check @Atlas.Codes.columnKernelHom_bijective
#print axioms Atlas.Codes.sextetColumnKernelEquiv
#print Atlas.Codes.sextetColumnKernelEquiv
#print axioms Atlas.Codes.sextetCoordinate_kernel_card
#check @Atlas.Codes.sextetCoordinate_kernel_card
#print axioms Atlas.Codes.sextetStabilizer
#print Atlas.Codes.sextetStabilizer
#print axioms Atlas.Codes.SextetStabilizer
#print Atlas.Codes.SextetStabilizer
#print axioms Atlas.Codes.sextetStabilizer_mem_iff
#check @Atlas.Codes.sextetStabilizer_mem_iff
#print axioms Atlas.Codes.hexAffineAction
#print Atlas.Codes.hexAffineAction
#print axioms Atlas.Codes.SextetAffineGroup
#print Atlas.Codes.SextetAffineGroup
#print axioms Atlas.Codes.sextetAffineHom
#print Atlas.Codes.sextetAffineHom
#print axioms Atlas.Codes.sextetAffineHom_bijective
#check @Atlas.Codes.sextetAffineHom_bijective
#print axioms Atlas.Codes.sextetAffineEquiv
#print Atlas.Codes.sextetAffineEquiv
#print axioms Atlas.Codes.sextetAffineEquiv_coordinates
#check @Atlas.Codes.sextetAffineEquiv_coordinates
#print axioms Atlas.Codes.sextetAffineEquiv_inverse_parameters
#check @Atlas.Codes.sextetAffineEquiv_inverse_parameters
#print axioms Atlas.Codes.sextetStabilizer_card
#check @Atlas.Codes.sextetStabilizer_card
#print axioms Atlas.Codes.sextet_coordinate_transitive
#check @Atlas.Codes.sextet_coordinate_transitive
#print axioms Atlas.Codes.golay_coordinate_transitive
#check @Atlas.Codes.golay_coordinate_transitive
#print axioms Atlas.Codes.pairedColumns
#print Atlas.Codes.pairedColumns
#print axioms Atlas.Codes.columnPairing
#print Atlas.Codes.columnPairing
#print axioms Atlas.Codes.distinguishedUnorderedTrio
#print Atlas.Codes.distinguishedUnorderedTrio
#print axioms Atlas.Codes.columnUnion
#print Atlas.Codes.columnUnion
#print axioms Atlas.Codes.mem_columnUnion
#check @Atlas.Codes.mem_columnUnion
#print axioms Atlas.Codes.columnUnion_injective
#check @Atlas.Codes.columnUnion_injective
#print axioms Atlas.Codes.columnUnion_pair
#check @Atlas.Codes.columnUnion_pair
#print axioms Atlas.Codes.trio_columnUnion
#check @Atlas.Codes.trio_columnUnion
#print axioms Atlas.Codes.affine_columnUnion
#check @Atlas.Codes.affine_columnUnion
#print axioms Atlas.Codes.affine_trio_iff_pairing
#check @Atlas.Codes.affine_trio_iff_pairing
#print axioms Atlas.Codes.sextet_trio_iff_pairing
#check @Atlas.Codes.sextet_trio_iff_pairing

/-! # Job 6, HU: structural hexacode uniqueness -/
#print axioms Atlas.Codes.IsHexMDS
#print Atlas.Codes.IsHexMDS
#print axioms Atlas.Codes.codeTripleProjection
#print Atlas.Codes.codeTripleProjection
#print axioms Atlas.Codes.codeTripleProjection_injective
#check @Atlas.Codes.codeTripleProjection_injective
#print axioms Atlas.Codes.codeTripleProjection_bijective
#check @Atlas.Codes.codeTripleProjection_bijective
#print axioms Atlas.Codes.code_three_zeros
#check @Atlas.Codes.code_three_zeros
#print axioms Atlas.Codes.lastThree
#print Atlas.Codes.lastThree
#print axioms Atlas.Codes.firstThree_ne_lastThree
#check @Atlas.Codes.firstThree_ne_lastThree
#print axioms Atlas.Codes.mdsInputEquiv
#print Atlas.Codes.mdsInputEquiv
#print axioms Atlas.Codes.mdsEncoder
#print Atlas.Codes.mdsEncoder
#print axioms Atlas.Codes.mdsEncoder_first
#check @Atlas.Codes.mdsEncoder_first
#print axioms Atlas.Codes.mdsCoefficient
#print Atlas.Codes.mdsCoefficient
#print axioms Atlas.Codes.mdsCoefficient_injective
#check @Atlas.Codes.mdsCoefficient_injective
#print axioms Atlas.Codes.mdsCoefficientEquiv
#print Atlas.Codes.mdsCoefficientEquiv
#print axioms Atlas.Codes.mdsEncoder_last
#check @Atlas.Codes.mdsEncoder_last
#print axioms Atlas.Codes.KleinMatrix
#print Atlas.Codes.KleinMatrix
#print axioms Atlas.Codes.kleinGraphWord
#print Atlas.Codes.kleinGraphWord
#print axioms Atlas.Codes.kleinGraphWord_first
#check @Atlas.Codes.kleinGraphWord_first
#print axioms Atlas.Codes.kleinGraphWord_last
#check @Atlas.Codes.kleinGraphWord_last
#print axioms Atlas.Codes.hexIndex_first_or_last
#check @Atlas.Codes.hexIndex_first_or_last
#print axioms Atlas.Codes.IsMDSMatrix
#print Atlas.Codes.IsMDSMatrix
#print axioms Atlas.Codes.mdsEncoder_graph
#check @Atlas.Codes.mdsEncoder_graph
#print axioms Atlas.Codes.mdsMatrix_valid
#check @Atlas.Codes.mdsMatrix_valid
#print axioms Atlas.Codes.normalizedKleinMatrix
#print Atlas.Codes.normalizedKleinMatrix
#print axioms Atlas.Codes.normalizedKleinMatrix_row
#check @Atlas.Codes.normalizedKleinMatrix_row
#print axioms Atlas.Codes.normalizedKleinMatrix_col
#check @Atlas.Codes.normalizedKleinMatrix_col
#print axioms Atlas.Codes.kleinNormalization
#print Atlas.Codes.kleinNormalization
#print axioms Atlas.Codes.kleinNormalization_first
#check @Atlas.Codes.kleinNormalization_first
#print axioms Atlas.Codes.kleinNormalization_last
#check @Atlas.Codes.kleinNormalization_last
#print axioms Atlas.Codes.kleinGraph_normalization
#check @Atlas.Codes.kleinGraph_normalization
#print axioms Atlas.Codes.normalizedKleinMatrix_valid
#check @Atlas.Codes.normalizedKleinMatrix_valid
#print axioms Atlas.Codes.kleinGraphWord_single_last
#check @Atlas.Codes.kleinGraphWord_single_last
#print axioms Atlas.Codes.kleinGraphWord_add
#check @Atlas.Codes.kleinGraphWord_add
#print axioms Atlas.Codes.mds_minor_kernel
#check @Atlas.Codes.mds_minor_kernel
#print axioms Atlas.Codes.normalized_fixed_free
#check @Atlas.Codes.normalized_fixed_free
#print axioms Atlas.Codes.kIsometry_fixed_free
#check @Atlas.Codes.kIsometry_fixed_free
#print axioms Atlas.Codes.normalized_coefficient_cycle
#check @Atlas.Codes.normalized_coefficient_cycle
#print axioms Atlas.Codes.normalized_row_distinct
#check @Atlas.Codes.normalized_row_distinct
#print axioms Atlas.Codes.normalized_col_distinct
#check @Atlas.Codes.normalized_col_distinct
#print axioms Atlas.Codes.kleinNormalMatrix
#print Atlas.Codes.kleinNormalMatrix
#print axioms Atlas.Codes.cycle_pair_inverse
#check @Atlas.Codes.cycle_pair_inverse
#print axioms Atlas.Codes.normalized_matrix_forced
#check @Atlas.Codes.normalized_matrix_forced
#print axioms Atlas.Codes.hexOrientationSwap
#print Atlas.Codes.hexOrientationSwap
#print axioms Atlas.Codes.hexOrientationSwap_first
#check @Atlas.Codes.hexOrientationSwap_first
#print axioms Atlas.Codes.hexOrientationSwap_last
#check @Atlas.Codes.hexOrientationSwap_last
#print axioms Atlas.Codes.kleinGraph_orientation
#check @Atlas.Codes.kleinGraph_orientation
#print axioms Atlas.Codes.KleinNormalWords
#print Atlas.Codes.KleinNormalWords
#print axioms Atlas.Codes.mds_graph_normal_form
#check @Atlas.Codes.mds_graph_normal_form
#print axioms Atlas.Codes.MonomiallyEquivalent
#print Atlas.Codes.MonomiallyEquivalent
#print axioms Atlas.Codes.mds_mem_graph
#check @Atlas.Codes.mds_mem_graph
#print axioms Atlas.Codes.hex_mds_normal_form
#check @Atlas.Codes.hex_mds_normal_form
#print axioms Atlas.Codes.hexacode_isHexMDS
#check @Atlas.Codes.hexacode_isHexMDS
#print axioms Atlas.Codes.hexacode_unique_of_dimension_minimum
#check @Atlas.Codes.hexacode_unique_of_dimension_minimum
#print axioms Atlas.Codes.selfDual_hex_finrank
#check @Atlas.Codes.selfDual_hex_finrank
#print axioms Atlas.Codes.hexacode_unique_even_selfDual
#check @Atlas.Codes.hexacode_unique_even_selfDual

-- Revised Job 6: arbitrary-sextet quotient and full marked reconstruction.
#print axioms Atlas.Codes.evenBlockEquiv
#print Atlas.Codes.evenBlockEquiv
#print axioms Atlas.Codes.evenBlockProjection
#print Atlas.Codes.evenBlockProjection
#print axioms Atlas.Codes.constantEvenBlock
#print Atlas.Codes.constantEvenBlock
#print axioms Atlas.Codes.evenBlockProjection_surjective
#check @Atlas.Codes.evenBlockProjection_surjective
#print axioms Atlas.Codes.evenBlockProjection_kernel
#check @Atlas.Codes.evenBlockProjection_kernel
#print axioms Atlas.Codes.evenBlockQuotientEquiv
#print Atlas.Codes.evenBlockQuotientEquiv
#print axioms Atlas.Codes.evenBlock_half_weight
#check @Atlas.Codes.evenBlock_half_weight
#print axioms Atlas.Codes.evenBlock_polar
#check @Atlas.Codes.evenBlock_polar
#print axioms Atlas.Codes.tetradGluingParity
#print Atlas.Codes.tetradGluingParity
#print axioms Atlas.Codes.tetradGluingParity_kernel
#check @Atlas.Codes.tetradGluingParity_kernel
#print axioms Atlas.Codes.tetradGluing
#print Atlas.Codes.tetradGluing
#print axioms Atlas.Codes.tetradGluing_apply
#check @Atlas.Codes.tetradGluing_apply
#print axioms Atlas.Codes.tetradGluing_mem_iff
#check @Atlas.Codes.tetradGluing_mem_iff
#print axioms Atlas.Codes.tetradGluing_represented
#check @Atlas.Codes.tetradGluing_represented
#print axioms Atlas.Codes.tetradRemainder
#print Atlas.Codes.tetradRemainder
#print axioms Atlas.Codes.tetradEven_decomposition
#check @Atlas.Codes.tetradEven_decomposition
#print axioms Atlas.Codes.tetradEven_change_constants
#check @Atlas.Codes.tetradEven_change_constants
#print axioms Atlas.Codes.j_constant_nonzero_weight
#check @Atlas.Codes.j_constant_nonzero_weight
#print axioms Atlas.Codes.tetradHexacode_minimum
#check @Atlas.Codes.tetradHexacode_minimum
#print axioms Atlas.Codes.tetradHexacode_unique
#check @Atlas.Codes.tetradHexacode_unique
#print axioms Atlas.Codes.tetradHexacode_even
#check @Atlas.Codes.tetradHexacode_even
#print axioms Atlas.Codes.IsTetradCode
#print Atlas.Codes.IsTetradCode
#print axioms Atlas.Codes.wholeTetrad
#print Atlas.Codes.wholeTetrad
#print axioms Atlas.Codes.wholeTetrad_weight
#check @Atlas.Codes.wholeTetrad_weight
#print axioms Atlas.Codes.wholeTetrad_ne_zero
#check @Atlas.Codes.wholeTetrad_ne_zero
#print axioms Atlas.Codes.wholeTetrad_dot
#check @Atlas.Codes.wholeTetrad_dot
#print axioms Atlas.Codes.wholeTetrad_pair_mem
#check @Atlas.Codes.wholeTetrad_pair_mem
#print axioms Atlas.Codes.tetradCode_orthogonal
#check @Atlas.Codes.tetradCode_orthogonal
#print axioms Atlas.Codes.tetradCode_common_parity
#check @Atlas.Codes.tetradCode_common_parity
#print axioms Atlas.Codes.tetradParity
#print Atlas.Codes.tetradParity
#print axioms Atlas.Codes.tetradCode_no_wholeTetrad
#check @Atlas.Codes.tetradCode_no_wholeTetrad
#print axioms Atlas.Codes.tetradCode_repetition_mem
#check @Atlas.Codes.tetradCode_repetition_mem
#print axioms Atlas.Codes.tetradParity_surjective
#check @Atlas.Codes.tetradParity_surjective
#print axioms Atlas.Codes.tetradEvenSubcode
#print Atlas.Codes.tetradEvenSubcode
#print axioms Atlas.Codes.tetradEvenSubcode_mem
#check @Atlas.Codes.tetradEvenSubcode_mem
#print axioms Atlas.Codes.tetradCode_finrank
#check @Atlas.Codes.tetradCode_finrank
#print axioms Atlas.Codes.tetradEvenSubcode_finrank
#check @Atlas.Codes.tetradEvenSubcode_finrank
#print axioms Atlas.Codes.tetradDecode
#print Atlas.Codes.tetradDecode
#print axioms Atlas.Codes.tetradHexacode
#print Atlas.Codes.tetradHexacode
#print axioms Atlas.Codes.tetradConstants
#print Atlas.Codes.tetradConstants
#print axioms Atlas.Codes.tetradConstants_injective
#check @Atlas.Codes.tetradConstants_injective
#print axioms Atlas.Codes.tetradDecode_kernel
#check @Atlas.Codes.tetradDecode_kernel
#print axioms Atlas.Codes.tetradQuotientEquiv
#print Atlas.Codes.tetradQuotientEquiv
#print axioms Atlas.Codes.tetradDecode_kernel_finrank
#check @Atlas.Codes.tetradDecode_kernel_finrank
#print axioms Atlas.Codes.tetradHexacode_finrank
#check @Atlas.Codes.tetradHexacode_finrank
#print axioms Atlas.Codes.tetradDecode_polar
#check @Atlas.Codes.tetradDecode_polar
#print axioms Atlas.Codes.tetradHexacode_selfDual
#check @Atlas.Codes.tetradHexacode_selfDual
#print axioms Atlas.Codes.permutedBinaryCode
#print Atlas.Codes.permutedBinaryCode
#print axioms Atlas.Codes.coordinatePermutation_dot
#check @Atlas.Codes.coordinatePermutation_dot
#print axioms Atlas.Codes.permutedBinaryCode_mem
#check @Atlas.Codes.permutedBinaryCode_mem
#print axioms Atlas.Codes.permutedBinaryCode_selfDual
#check @Atlas.Codes.permutedBinaryCode_selfDual
#print axioms Atlas.Codes.affinePermutation_repetition
#check @Atlas.Codes.affinePermutation_repetition
#print axioms Atlas.Codes.affinePermutation_R0
#check @Atlas.Codes.affinePermutation_R0
#print axioms Atlas.Codes.permutedTetradCode
#check @Atlas.Codes.permutedTetradCode
#print axioms Atlas.Codes.polarConstants
#print Atlas.Codes.polarConstants
#print axioms Atlas.Codes.polarConstants_sum
#check @Atlas.Codes.polarConstants_sum
#print axioms Atlas.Codes.affineTranslation_normalizes
#check @Atlas.Codes.affineTranslation_normalizes
#print axioms Atlas.Codes.tetradGluing_normalization
#check @Atlas.Codes.tetradGluing_normalization
#print axioms Atlas.Codes.tetradCode_normalized
#check @Atlas.Codes.tetradCode_normalized
#print axioms Atlas.Codes.monomialMarkedCode_lift
#check @Atlas.Codes.monomialMarkedCode_lift
#print axioms Atlas.Codes.permutedBinaryCode_finrank
#check @Atlas.Codes.permutedBinaryCode_finrank
#print axioms Atlas.Codes.tetradCode_equivalent
#check @Atlas.Codes.tetradCode_equivalent
#print axioms Atlas.Codes.blockWordDecode
#print Atlas.Codes.blockWordDecode
#print axioms Atlas.Codes.blockWordConstants
#print Atlas.Codes.blockWordConstants
#print axioms Atlas.Codes.evenWord_decomposition
#check @Atlas.Codes.evenWord_decomposition
#print axioms Atlas.Codes.binaryWord_add_self
#check @Atlas.Codes.binaryWord_add_self
#print axioms Atlas.Codes.oddWord_decode_mem
#check @Atlas.Codes.oddWord_decode_mem
#print axioms Atlas.Codes.eta_wrong_extension_weight
#check @Atlas.Codes.eta_wrong_extension_weight
#print axioms Atlas.Codes.normalizedTetradCode_eta
#check @Atlas.Codes.normalizedTetradCode_eta
#print axioms Atlas.Codes.normalizedTetradCode_even_decode
#check @Atlas.Codes.normalizedTetradCode_even_decode
#print axioms Atlas.Codes.normalizedTetradCode_mem
#check @Atlas.Codes.normalizedTetradCode_mem
#print axioms Atlas.Codes.sextetRows
#print Atlas.Codes.sextetRows
#print axioms Atlas.Codes.sextetCoordinates
#print Atlas.Codes.sextetCoordinates
#print axioms Atlas.Codes.sextetCoordinates_tetrad
#check @Atlas.Codes.sextetCoordinates_tetrad
#print axioms Atlas.Codes.sextetCoordinates_parts
#check @Atlas.Codes.sextetCoordinates_parts
#print axioms Atlas.Codes.wholeTetrad_pair_support
#check @Atlas.Codes.wholeTetrad_pair_support
#print axioms Atlas.Codes.sextetCoordinates_pair_mem
#check @Atlas.Codes.sextetCoordinates_pair_mem
#print axioms Atlas.Codes.sextet_marked_reconstruction
#check @Atlas.Codes.sextet_marked_reconstruction
#print axioms Atlas.Codes.sextet_equivalent_distinguished
#check @Atlas.Codes.sextet_equivalent_distinguished
#print axioms Atlas.Codes.R0_le_of_pairs
#check @Atlas.Codes.R0_le_of_pairs
#print axioms Atlas.Codes.sextetCode
#print Atlas.Codes.sextetCode
#print axioms Atlas.Codes.sextetCode_properties
#check @Atlas.Codes.sextetCode_properties
#print axioms Atlas.Codes.sextetHexacode
#print Atlas.Codes.sextetHexacode
#print axioms Atlas.Codes.sextetHexacode_properties
#check @Atlas.Codes.sextetHexacode_properties

-- Revised Job 6 SO: reconstruction-derived sextet orbit and full group order.
#print axioms Atlas.Codes.sextet_from_distinguished
#check @Atlas.Codes.sextet_from_distinguished
#print axioms Atlas.Codes.unorderedSextet_pretransitive
#check @Atlas.Codes.unorderedSextet_pretransitive
#print axioms Atlas.Codes.sextetOrbitEquiv
#print Atlas.Codes.sextetOrbitEquiv
#print axioms Atlas.Codes.sextetOrbitStabilizerEquiv
#print Atlas.Codes.sextetOrbitStabilizerEquiv
#print axioms Atlas.Codes.mathieu24_order
#check @Atlas.Codes.mathieu24_order
#print axioms Atlas.Codes.mathieu24_order_factorization
#check @Atlas.Codes.mathieu24_order_factorization
#print axioms Atlas.Codes.sextetStabilizer_index
#check @Atlas.Codes.sextetStabilizer_index

-- Revised Job 6 PA: local stabilizers, five-transitivity, parity, and public package.
#print axioms Atlas.Codes.klein_subgroup_full
#check @Atlas.Codes.klein_subgroup_full
#print axioms Atlas.Codes.klein_cycle_inverter_noncyclic
#check @Atlas.Codes.klein_cycle_inverter_noncyclic
#print axioms Atlas.Codes.klein_subgroup_full_of_inverter
#check @Atlas.Codes.klein_subgroup_full_of_inverter
#print axioms Atlas.Codes.HexEvenPoint
#print Atlas.Codes.HexEvenPoint
#print axioms Atlas.Codes.hex_even_coordinate_transitive
#check @Atlas.Codes.hex_even_coordinate_transitive
#print axioms Atlas.Codes.hexEvenPointOrbitEquiv
#print Atlas.Codes.hexEvenPointOrbitEquiv
#print axioms Atlas.Codes.hexEvenPoint_card
#check @Atlas.Codes.hexEvenPoint_card
#print axioms Atlas.Codes.hexPointKernelAlternating
#print Atlas.Codes.hexPointKernelAlternating
#print axioms Atlas.Codes.hexPointKernelAlternating_bijective
#check @Atlas.Codes.hexPointKernelAlternating_bijective
#print axioms Atlas.Codes.hexPointKernelAlternatingEquiv
#print Atlas.Codes.hexPointKernelAlternatingEquiv
#print axioms Atlas.Codes.hexPointKernel_coordinate_image
#check @Atlas.Codes.hexPointKernel_coordinate_image
#print axioms Atlas.Codes.hexPointKernel_transitive_complement
#check @Atlas.Codes.hexPointKernel_transitive_complement
#print axioms Atlas.Codes.klein_cycle_ne_one
#check @Atlas.Codes.klein_cycle_ne_one
#print axioms Atlas.Codes.klein_cycle_square_ne_one
#check @Atlas.Codes.klein_cycle_square_ne_one
#print axioms Atlas.Codes.klein_cycle_ne_inverse
#check @Atlas.Codes.klein_cycle_ne_inverse
#print axioms Atlas.Codes.hexPointKernel_even
#check @Atlas.Codes.hexPointKernel_even
#print axioms Atlas.Codes.hexPointKernel_coordinate_one
#check @Atlas.Codes.hexPointKernel_coordinate_one
#print axioms Atlas.Codes.hexPointKernelCoordinate
#print Atlas.Codes.hexPointKernelCoordinate
#print axioms Atlas.Codes.hexPointKernelCoordinate_injective
#check @Atlas.Codes.hexPointKernelCoordinate_injective
#print axioms Atlas.Codes.hexCoordinateAction
#print Atlas.Codes.hexCoordinateAction
#print axioms Atlas.Codes.hexCoordinateAction_transitive
#check @Atlas.Codes.hexCoordinateAction_transitive
#print axioms Atlas.Codes.hexPointOrbitEquiv
#print Atlas.Codes.hexPointOrbitEquiv
#print axioms Atlas.Codes.hexPointOrbitStabilizerEquiv
#print Atlas.Codes.hexPointOrbitStabilizerEquiv
#print axioms Atlas.Codes.hexPointStabilizer_card
#check @Atlas.Codes.hexPointStabilizer_card
#print axioms Atlas.Codes.hexPointKernel
#print Atlas.Codes.hexPointKernel
#print axioms Atlas.Codes.hexPointKernel_card
#check @Atlas.Codes.hexPointKernel_card
#print axioms Atlas.Codes.hexPointStabilizer
#print Atlas.Codes.hexPointStabilizer
#print axioms Atlas.Codes.hexPointStabilizer_fixed
#check @Atlas.Codes.hexPointStabilizer_fixed
#print axioms Atlas.Codes.hexPointStabilizer_inv_fixed
#check @Atlas.Codes.hexPointStabilizer_inv_fixed
#print axioms Atlas.Codes.hexPointLocal
#print Atlas.Codes.hexPointLocal
#print axioms Atlas.Codes.hexPointZ
#print Atlas.Codes.hexPointZ
#print axioms Atlas.Codes.hexPointZ_cycle
#check @Atlas.Codes.hexPointZ_cycle
#print axioms Atlas.Codes.hexSign_coordinate
#check @Atlas.Codes.hexSign_coordinate
#print axioms Atlas.Codes.hexPoint_odd_exists
#check @Atlas.Codes.hexPoint_odd_exists
#print axioms Atlas.Codes.hexPointLocal_surjective
#check @Atlas.Codes.hexPointLocal_surjective
#print axioms Atlas.Codes.hexZeroCoordinate
#print Atlas.Codes.hexZeroCoordinate
#print axioms Atlas.Codes.hexZeroCoordinate_card
#check @Atlas.Codes.hexZeroCoordinate_card
#print axioms Atlas.Codes.hexZeroCoordinate_other_surjective
#check @Atlas.Codes.hexZeroCoordinate_other_surjective
#print axioms Atlas.Codes.hexZeroAct
#print Atlas.Codes.hexZeroAct
#print axioms Atlas.Codes.hexZeroLinear
#print Atlas.Codes.hexZeroLinear
#print axioms Atlas.Codes.hexZeroAffineAction
#print Atlas.Codes.hexZeroAffineAction
#print axioms Atlas.Codes.TetradPointAffine
#print Atlas.Codes.TetradPointAffine
#print axioms Atlas.Codes.hexZeroInclusion
#print Atlas.Codes.hexZeroInclusion
#print axioms Atlas.Codes.tetradPointAffineInclusion
#print Atlas.Codes.tetradPointAffineInclusion
#print axioms Atlas.Codes.tetradPointAffine_card
#check @Atlas.Codes.tetradPointAffine_card
#print axioms Atlas.Codes.rowTranslation
#print Atlas.Codes.rowTranslation
#print axioms Atlas.Codes.rowTranslation_even
#check @Atlas.Codes.rowTranslation_even
#print axioms Atlas.Codes.affineTranslation_even
#check @Atlas.Codes.affineTranslation_even
#print axioms Atlas.Codes.sextetSign
#print Atlas.Codes.sextetSign
#print axioms Atlas.Codes.sextetSection_Z_even
#check @Atlas.Codes.sextetSection_Z_even
#print axioms Atlas.Codes.sextetSection_lift_even
#check @Atlas.Codes.sextetSection_lift_even
#print axioms Atlas.Codes.sextetSection_even
#check @Atlas.Codes.sextetSection_even
#print axioms Atlas.Codes.sextetTranslation_even
#check @Atlas.Codes.sextetTranslation_even
#print axioms Atlas.Codes.sextetStabilizer_even
#check @Atlas.Codes.sextetStabilizer_even
#print axioms Atlas.Codes.mathieu24Sign
#print Atlas.Codes.mathieu24Sign
#print axioms Atlas.Codes.mathieu24_even
#check @Atlas.Codes.mathieu24_even
#print axioms Atlas.Codes.mathieu24_le_alternating
#check @Atlas.Codes.mathieu24_le_alternating
#print axioms Atlas.Codes.Mathieu24HexacodeConstructionPackage
#print Atlas.Codes.Mathieu24HexacodeConstructionPackage
#print axioms Atlas.Codes.mathieu24_hexacode_construction
#check @Atlas.Codes.mathieu24_hexacode_construction
#print axioms Atlas.Codes.tetradPointStabilizer_complement_transitive
#check @Atlas.Codes.tetradPointStabilizer_complement_transitive
#print axioms Atlas.Codes.firstFourEmbedding
#print Atlas.Codes.firstFourEmbedding
#print axioms Atlas.Codes.orderedFive_last_outside
#check @Atlas.Codes.orderedFive_last_outside
#print axioms Atlas.Codes.mathieu24_five_transitive_explicit
#check @Atlas.Codes.mathieu24_five_transitive_explicit
#print axioms Atlas.Codes.mathieu24_five_transitive
#check @Atlas.Codes.mathieu24_five_transitive
#print axioms Atlas.Codes.fourSet_to_tetrad
#check @Atlas.Codes.fourSet_to_tetrad
#print axioms Atlas.Codes.orderedFour_to_tetrad
#check @Atlas.Codes.orderedFour_to_tetrad
#print axioms Atlas.Codes.mathieu24_four_transitive_explicit
#check @Atlas.Codes.mathieu24_four_transitive_explicit
#print axioms Atlas.Codes.mathieu24_four_transitive
#check @Atlas.Codes.mathieu24_four_transitive
#print axioms Atlas.Codes.hexZ_local_fixed
#check @Atlas.Codes.hexZ_local_fixed
#print axioms Atlas.Codes.hexZ_moves_nonzero
#check @Atlas.Codes.hexZ_moves_nonzero
#print axioms Atlas.Codes.hexZ_translation_noncommute
#check @Atlas.Codes.hexZ_translation_noncommute
#print axioms Atlas.Codes.mathieu24_noncommuting_pair
#check @Atlas.Codes.mathieu24_noncommuting_pair
#print axioms Atlas.Codes.ContainedInOctad
#print Atlas.Codes.ContainedInOctad
#print axioms Atlas.Codes.containedInOctad_permute
#check @Atlas.Codes.containedInOctad_permute
#print axioms Atlas.Codes.sixSet_octad_obstruction
#check @Atlas.Codes.sixSet_octad_obstruction
#print axioms Atlas.Codes.mathieu24_not_six_homogeneous
#check @Atlas.Codes.mathieu24_not_six_homogeneous
#print axioms Atlas.Codes.finiteSetLabelling
#print Atlas.Codes.finiteSetLabelling
#print axioms Atlas.Codes.finiteSetEmbedding
#print Atlas.Codes.finiteSetEmbedding
#print axioms Atlas.Codes.finiteSetEmbedding_image
#check @Atlas.Codes.finiteSetEmbedding_image
#print axioms Atlas.Codes.mathieu24_not_six_transitive
#check @Atlas.Codes.mathieu24_not_six_transitive
#print axioms Atlas.Codes.orderedPointStabilizer
#print Atlas.Codes.orderedPointStabilizer
#print axioms Atlas.Codes.orderedPointStabilizer_order_product
#check @Atlas.Codes.orderedPointStabilizer_order_product
#print axioms Atlas.Codes.mathieu24_one_point_order
#check @Atlas.Codes.mathieu24_one_point_order
#print axioms Atlas.Codes.mathieu24_two_point_order
#check @Atlas.Codes.mathieu24_two_point_order
#print axioms Atlas.Codes.mathieu24_three_point_order
#check @Atlas.Codes.mathieu24_three_point_order
#print axioms Atlas.Codes.mathieu24_four_point_order
#check @Atlas.Codes.mathieu24_four_point_order
#print axioms Atlas.Codes.mathieu24_five_point_order
#check @Atlas.Codes.mathieu24_five_point_order
#print axioms Atlas.Codes.sextet_tetrad_affine_full
#check @Atlas.Codes.sextet_tetrad_affine_full
#print axioms Atlas.Codes.sextet_tetrad_full_symmetric
#check @Atlas.Codes.sextet_tetrad_full_symmetric
#print axioms Atlas.Codes.tetrad_stabilizer_preserves_sextet
#check @Atlas.Codes.tetrad_stabilizer_preserves_sextet
#print axioms Atlas.Codes.TetradPointStabilizer
#print Atlas.Codes.TetradPointStabilizer
#print axioms Atlas.Codes.tetradPointStabilizer_mem
#check @Atlas.Codes.tetradPointStabilizer_mem
#print axioms Atlas.Codes.tetradPointStabilizer_le_sextet
#check @Atlas.Codes.tetradPointStabilizer_le_sextet
#print axioms Atlas.Codes.sextetAffine_fixes_tetrad
#check @Atlas.Codes.sextetAffine_fixes_tetrad
#print axioms Atlas.Codes.tetradPointAffineHom
#print Atlas.Codes.tetradPointAffineHom
#print axioms Atlas.Codes.tetradPointAffineHom_bijective
#check @Atlas.Codes.tetradPointAffineHom_bijective
#print axioms Atlas.Codes.tetradPointStabilizerEquiv
#print Atlas.Codes.tetradPointStabilizerEquiv
#print axioms Atlas.Codes.tetradPointStabilizer_card
#check @Atlas.Codes.tetradPointStabilizer_card
#print axioms Atlas.Sporadic.Mathieu24.Model
#print Atlas.Sporadic.Mathieu24.Model
#print axioms Atlas.Sporadic.Mathieu24.Points
#print Atlas.Sporadic.Mathieu24.Points
#print axioms Atlas.Sporadic.Mathieu24.finite
#check @Atlas.Sporadic.Mathieu24.finite
#print axioms Atlas.Sporadic.Mathieu24.order
#check @Atlas.Sporadic.Mathieu24.order
#print axioms Atlas.Sporadic.Mathieu24.faithful
#check @Atlas.Sporadic.Mathieu24.faithful
#print axioms Atlas.Sporadic.Mathieu24.five_transitive
#check @Atlas.Sporadic.Mathieu24.five_transitive
#print axioms Atlas.Sporadic.Mathieu24.not_six_transitive
#check @Atlas.Sporadic.Mathieu24.not_six_transitive
#print axioms Atlas.Sporadic.Mathieu24.noncommuting_pair
#check @Atlas.Sporadic.Mathieu24.noncommuting_pair
#print axioms Atlas.Sporadic.Mathieu24.alternating
#check @Atlas.Sporadic.Mathieu24.alternating
#print axioms Atlas.Sporadic.Mathieu24.construction
#check @Atlas.Sporadic.Mathieu24.construction

/- Cyclic family: standard residue model and translation action. -/
#print axioms Atlas.Families.Cyclic.finite
#print axioms Atlas.Families.Cyclic.card
#print axioms Atlas.Families.Cyclic.commutative
#print axioms Atlas.Families.Cyclic.cyclic
#print axioms Atlas.Families.Cyclic.generator_order
#print axioms Atlas.Families.Cyclic.generator_generates
#print axioms Atlas.Families.Cyclic.isSimpleGroup_iff
#print axioms Atlas.Families.Cyclic.isSimpleGroup
#print axioms Atlas.Families.Cyclic.translation
#print axioms Atlas.Families.Cyclic.translation_mul
#print axioms Atlas.Families.Cyclic.regular
#print axioms Atlas.Families.Cyclic.faithful
#print axioms Atlas.Families.Cyclic.transitive
#print axioms Atlas.Families.Cyclic.simple_iff_exists_prime_model
#print axioms Atlas.Families.Cyclic.not_simple_one
#print axioms Atlas.Families.Cyclic.simple_two
#print axioms Atlas.Families.Cyclic.simple_three
#print axioms Atlas.Families.Cyclic.not_simple_four
#print axioms Atlas.Families.Cyclic.construction
#print axioms Atlas.Families.Cyclic.exists_model

/- Alternating family: actual sign kernel, actions and pointwise stabilizers. -/
#print axioms Atlas.Families.Alternating.multiply_transitive
#print axioms Atlas.Families.Alternating.not_multiply_transitive
#print axioms Atlas.Families.Alternating.IsAdmissible
#print axioms Atlas.Families.Alternating.order
#print axioms Atlas.Families.Alternating.finite
#print axioms Atlas.Families.Alternating.normal
#print axioms Atlas.Families.Alternating.index
#print axioms Atlas.Families.Alternating.card_mul_two
#print axioms Atlas.Families.Alternating.card_factorial
#print axioms Atlas.Families.Alternating.factorial_divisible
#print axioms Atlas.Families.Alternating.trivial_small
#print axioms Atlas.Families.Alternating.card
#print axioms Atlas.Families.Alternating.isSimpleGroup
#print axioms Atlas.Families.Alternating.exists_mul_ne_mul
#print axioms Atlas.Families.Alternating.cyclic_three
#print axioms Atlas.Families.Alternating.simple_three
#print axioms Atlas.Families.Alternating.threeEquivCyclic
#print axioms Atlas.Families.Alternating.not_simple_four
#print axioms Atlas.Families.Alternating.not_simple_small
#print axioms Atlas.Families.Alternating.isSimpleGroup_iff
#print axioms Atlas.Families.Alternating.nonabelian_simple_iff
#print axioms Atlas.Families.Alternating.faithful
#print axioms Atlas.Families.Alternating.action_apply
#print axioms Atlas.Families.Alternating.generation
#print axioms Atlas.Families.Alternating.relabel
#print axioms Atlas.Families.Alternating.relabel_apply
#print axioms Atlas.Families.Alternating.construction
#print axioms Atlas.Families.Alternating.exists_model
#print axioms Atlas.Families.Alternating.checks_five
#print axioms Atlas.Families.Alternating.checks_six
#print axioms Atlas.Families.Alternating.checks_seven
#print axioms Atlas.Families.Alternating.checks_eight
#print axioms Atlas.Families.Alternating.checks_small
#print axioms Atlas.Families.Alternating.extension_range
#print axioms Atlas.Families.Alternating.stabilizerComplementEquiv
#print axioms Atlas.Families.Alternating.stabilizerComplementEquiv_extension
#print axioms Atlas.Families.Alternating.stabilizerComplementEquiv_apply
#print axioms Atlas.Families.Alternating.tuplePoints
#print axioms Atlas.Families.Alternating.mem_pointwiseStabilizer
#print axioms Atlas.Families.Alternating.complement_card
#print axioms Atlas.Families.Alternating.stabilizerEquiv
#print axioms Atlas.Families.Alternating.stabilizer_card
#print axioms Atlas.Families.Alternating.stabilizer_card_factorial
#print axioms Atlas.Families.Alternating.stabilizer_card_one
#print axioms Atlas.Families.Alternating.stabilizer_trivial

#print axioms Atlas.GroupTheory.normal_pretransitive
#print axioms Atlas.GroupTheory.stabilizer_complement_faithful
#print axioms Atlas.GroupTheory.prime_degree_normalizer_arithmetic
#print axioms Atlas.GroupTheory.sylow_card_prime
#print axioms Atlas.GroupTheory.prime_subgroup_eq_zpowers
#print axioms Atlas.GroupTheory.prime_order_fixedPointFree
#print axioms Atlas.GroupTheory.prime_subgroup_pretransitive
#print axioms Atlas.GroupTheory.normalizer_action_injective
#print axioms Atlas.GroupTheory.prime_normalizer_card_bound
#print axioms Atlas.GroupTheory.sylow_nonidentity_injective
#print axioms Atlas.GroupTheory.sylow_nonidentity_card
#print axioms Atlas.GroupTheory.sylow_count_one_of_card
#print axioms Atlas.GroupTheory.sylow_card_subgroup_of_all_le
#print axioms Atlas.GroupTheory.sylow_le_normal_of_prime_dvd
#print axioms Atlas.GroupTheory.sylow_normalizer_factor
#print axioms Atlas.GroupTheory.prime_degree_simple
#print axioms Atlas.Codes.Mathieu23PointModel
#print axioms Atlas.Codes.Mathieu23Points
#print axioms Atlas.Codes.mathieu23_embedding
#print axioms Atlas.Codes.mathieu23_embedding_injective
#print axioms Atlas.Codes.mathieu23_degree
#print axioms Atlas.Codes.mathieu23_faithful
#print axioms Atlas.Codes.mathieu23_four_transitive
#print axioms Atlas.Codes.mathieu23_order
#print axioms Atlas.Codes.mathieu23_simple
#print axioms Atlas.Codes.mathieu23_noncommuting_pair

#print axioms Atlas.GroupTheory.regular_normal_impossible
#print axioms Atlas.GroupTheory.simple_of_simple_stabilizer
#print axioms Atlas.Codes.mathieu24_simple
#print axioms Atlas.Codes.mathieu24_nonabelian_simple

#print axioms Atlas.Sporadic.Mathieu24.card
#print axioms Atlas.Sporadic.Mathieu24.isSimpleGroup
#print axioms Atlas.Sporadic.Mathieu24.exists_mul_ne_mul
#print axioms Atlas.Sporadic.Mathieu24.card_factorization
#print axioms Atlas.Sporadic.Mathieu24.code_design_automorphisms
#print axioms Atlas.Sporadic.Mathieu24.octads_design
#print axioms Atlas.Sporadic.Mathieu24.sextet_transitive
#print axioms Atlas.Sporadic.Mathieu24.sextet_count
#print axioms Atlas.Sporadic.Mathieu24.sextet_stabilizer_order
#print axioms Atlas.Sporadic.Mathieu24.pointwise_stabilizer_order_product
#print axioms Atlas.Sporadic.Mathieu24.construction_complete
#print axioms Atlas.Sporadic.Mathieu24.exists_model
#print axioms Atlas.Sporadic.Mathieu23.embedding_injective
#print axioms Atlas.Sporadic.Mathieu23.finite
#print axioms Atlas.Sporadic.Mathieu23.card
#print axioms Atlas.Sporadic.Mathieu23.degree
#print axioms Atlas.Sporadic.Mathieu23.faithful
#print axioms Atlas.Sporadic.Mathieu23.four_transitive
#print axioms Atlas.Sporadic.Mathieu23.isSimpleGroup
#print axioms Atlas.Sporadic.Mathieu23.exists_mul_ne_mul
#print axioms Atlas.Sporadic.Mathieu23.conjugacyPoints_bijective
#print axioms Atlas.Sporadic.Mathieu23.exists_conjugacy
#print axioms Atlas.Sporadic.Mathieu23.construction

#print axioms Atlas.Codes.mathieu23_orbitEquiv
#print axioms Atlas.Codes.mathieu23_index_product
#print axioms Atlas.Codes.mathieu23_order_factorization
#print axioms Atlas.Codes.mathieu23_not_five_transitive
#print axioms Atlas.Codes.mathieu23TupleStabilizer_order_product
#print axioms Atlas.Codes.mathieu23_1_point_order
#print axioms Atlas.Codes.mathieu23_2_point_order
#print axioms Atlas.Codes.mathieu23_3_point_order
#print axioms Atlas.Codes.mathieu23_4_point_order
#print axioms Atlas.Codes.golay_parity_recovery
#print axioms Atlas.Codes.puncture_golay_injective
#print axioms Atlas.Codes.puncturedGolay_finrank
#print axioms Atlas.Codes.puncturedGolay_card
#print axioms Atlas.Codes.puncturedGolay_minimum
#print axioms Atlas.Codes.puncturedGolay_minimum_witness
#print axioms Atlas.Codes.golay_mem_iff_puncture_parity
#print axioms Atlas.Codes.puncturedRestriction_lift
#print axioms Atlas.Codes.puncturedLift_restriction
#print axioms Atlas.Codes.puncturedGolayAutEquiv
#print axioms Atlas.Codes.puncturedGolayAutEquiv_apply
#print axioms Atlas.Combinatorics.steiner_block_count
#print axioms Atlas.Codes.mathieu23Block_restore
#print axioms Atlas.Codes.mathieu23Blocks_size
#print axioms Atlas.Codes.mathieu23_steiner
#print axioms Atlas.Codes.mathieu23Blocks_card
#print axioms Atlas.Codes.mathieu23BlockLift_permute
#print axioms Atlas.Codes.mathieu23Blocks_preserved
#print axioms Atlas.Sporadic.Mathieu23.card_factorization
#print axioms Atlas.Sporadic.Mathieu23.index_product
#print axioms Atlas.Sporadic.Mathieu23.not_five_transitive
#print axioms Atlas.Sporadic.Mathieu23.puncturedCodeAutEquiv
#print axioms Atlas.Sporadic.Mathieu23.construction_complete
#print axioms Atlas.Sporadic.Mathieu23.exists_model
#print axioms Atlas.GroupTheory.card_eq_degree_of_commutative
#print axioms Atlas.Combinatorics.derived_steiner
#print axioms Atlas.Codes.mathieu22_order
#print axioms Atlas.Codes.mathieu22_index_product
#print axioms Atlas.Codes.mathieu22_ambient_index_product
#print axioms Atlas.Codes.mathieu22_order_factorization
#print axioms Atlas.Codes.mathieu22_image
#print axioms Atlas.Codes.mathieu22_faithful
#print axioms Atlas.Codes.mathieu22_three_transitive
#print axioms Atlas.Codes.mathieu22_not_four_transitive
#print axioms Atlas.Codes.mathieu22_noncommuting_pair
#print axioms Atlas.Codes.mathieu22TupleStabilizer_order_product
#print axioms Atlas.Codes.mathieu22_one_point_order
#print axioms Atlas.Codes.mathieu22_two_point_order
#print axioms Atlas.Codes.mathieu22_three_point_order
#print axioms Atlas.Codes.mathieu22_steiner
#print axioms Atlas.Codes.mathieu22Blocks_size
#print axioms Atlas.Codes.mathieu22Blocks_card
#print axioms Atlas.Codes.mathieu22Blocks_mem
#print axioms Atlas.Codes.mathieu22Blocks_preserved
#print axioms Atlas.Sporadic.Mathieu22.embedding_compatible
#print axioms Atlas.Codes.hexPointKernel_nonzero_transitive
#print axioms Atlas.Codes.hexZeroAffineAction_injective
#print axioms Atlas.Codes.hexZero_invariant_subgroup
#print axioms Atlas.Codes.hexFiberStabilizer_card
#print axioms Atlas.Codes.hexFiberPermutation_range
#print axioms Atlas.Codes.hexFiberPermutation_kernel_natural
#print axioms Atlas.Codes.hexFiberKernel_regular
#print axioms Atlas.Codes.tetradPointTranslations_centralizer
#print axioms Atlas.Codes.tetradPoint_normal_subgroups
#print axioms Atlas.Codes.mathieu21_order
#print axioms Atlas.Codes.mathieu21_simple
#print axioms Atlas.Codes.mathieu21_faithful
#print axioms Atlas.Codes.mathieu21_two_transitive
#print axioms Atlas.Codes.mathieu21_noncommuting_pair
#print axioms Atlas.Codes.mathieu21_embedding_injective
#print axioms Atlas.Codes.mathieu21LocalEquiv
#print axioms Atlas.Codes.tetradPoint_no_faithful_eight
#print axioms Atlas.GroupTheory.normalSylowSevenPermutation_injective
#print axioms Atlas.Codes.mathieu22_simple
#print axioms Atlas.Sporadic.Mathieu22.isSimpleGroup
#print axioms Atlas.Codes.mathieu22Pair_order
#print axioms Atlas.Codes.mathieu22PairRestriction_surjective
#print axioms Atlas.Codes.mathieu22Pair_kernel_index
#print axioms Atlas.Codes.mathieu22_to_pair_range
#print axioms Atlas.Codes.mathieu22Pair_faithful
#print axioms Atlas.Codes.mathieu22PairBlocks_preserved
#print axioms Atlas.Codes.mathieu22ChoiceEquiv_embedding
#print axioms Atlas.Codes.mathieu22Choice_equivariant
#print axioms Atlas.Codes.mathieu22Choice_exists
#print axioms Atlas.Sporadic.Mathieu22.construction_complete
#print axioms Atlas.Sporadic.Mathieu22.exists_model
#print axioms Atlas.Codes.dodecads_card
#print axioms Atlas.Codes.dodecad_parameters_exist
#print axioms Atlas.Codes.dodecad_parameters_converse
#print axioms Atlas.Codes.dodecad_parameters_unique
#print axioms Atlas.Codes.dodecad_parameters_block_shape
#print axioms Atlas.Codes.dodecadParametersEquiv
#print axioms Atlas.Codes.dodecadsThroughTetrad_card
#print axioms Atlas.Codes.dodecadMaskMap_kernel
#print axioms Atlas.Codes.dodecadMaskMap_range
#print axioms Atlas.Codes.dodecad_parameter_mask_odd
#print axioms Atlas.Codes.dodecad_translation_actual
#print axioms Atlas.Codes.dodecad_local_transitive
#print axioms Atlas.Codes.dodecad_ordered_flags_transitive
#print axioms Atlas.Codes.dodecad_transitive_explicit
#print axioms Atlas.Codes.dodecadOrbitStabilizerEquiv
#print axioms Atlas.Codes.mathieu12_order
#print axioms Atlas.Codes.mathieu12_order_factorization
#print axioms Atlas.Codes.mathieu12_order_from_four_points
#print axioms Atlas.Codes.mathieu12_four_transitive
#print axioms Atlas.Codes.dodecad_five_fixed
#print axioms Atlas.Codes.mathieu12_sharp_five_transitive
#print axioms Atlas.Codes.mathieu12_faithful
#print axioms Atlas.Codes.mathieu12_not_six_transitive
#print axioms Atlas.Codes.dodecadKleinProjection_surjective
#print axioms Atlas.Codes.dodecadProjectionKernelEquiv
#print axioms Atlas.Codes.dodecadKleinProjection_kernel_card
#print axioms Atlas.Codes.dodecadAffineStabilizer_card
#print axioms Atlas.Codes.dodecadRemaining_regular
#print axioms Atlas.Codes.dodecadFourAffineEquiv_coordinates
#print axioms Atlas.Codes.dodecadFourFixing_card
#print axioms Atlas.Codes.mathieu12_one_point_order
#print axioms Atlas.Codes.mathieu12_two_point_order
#print axioms Atlas.Codes.mathieu12_three_point_order
#print axioms Atlas.Codes.mathieu12_four_point_order
#print axioms Atlas.Codes.mathieu12_five_point_order
#print axioms Atlas.Codes.mathieu12Blocks_mem
#print axioms Atlas.Codes.mathieu12Blocks_size
#print axioms Atlas.Codes.mathieu12_steiner
#print axioms Atlas.Codes.mathieu12Blocks_card
#print axioms Atlas.Codes.mathieu12_hexad_determines_octad
#print axioms Atlas.Codes.mathieu12Blocks_preserved
#print axioms Atlas.Codes.mathieu12Blocks_complement
#print axioms Atlas.Codes.mathieu11_order
#print axioms Atlas.Codes.mathieu11_order_factorization
#print axioms Atlas.Codes.mathieu11_degree
#print axioms Atlas.Codes.mathieu11_faithful
#print axioms Atlas.Codes.mathieu11_sharp_four_transitive
#print axioms Atlas.Codes.mathieu11_noncommuting_pair
#print axioms Atlas.Codes.mathieu11_simple
#print axioms Atlas.Codes.mathieu11_index
#print axioms Atlas.Codes.mathieu11_order_product
#print axioms Atlas.Codes.mathieu12_simple
#print axioms Atlas.Codes.mathieu12_noncommuting_pair
#print axioms Atlas.Codes.mathieu12_nonabelian_simple
#print axioms Atlas.Codes.dodecad_complement
#print axioms Atlas.Codes.mathieu12_complement_stabilizer
#print axioms Atlas.Codes.mathieu12Pair_order
#print axioms Atlas.Codes.mathieu12PairRestriction_surjective
#print axioms Atlas.Codes.mathieu12PairKernelEquiv
#print axioms Atlas.Codes.mathieu12_to_pair_embedding
#print axioms Atlas.Codes.mathieu12_to_pair_range
#print axioms Atlas.Codes.mathieu12_pair_index
#print axioms Atlas.Codes.mathieu12Choice_embedding
#print axioms Atlas.Codes.mathieu12Choice_equivariant
#print axioms Atlas.Codes.mathieu12Choice_blocks
#print axioms Atlas.Codes.dodecad_point_flags_transitive
#print axioms Atlas.Codes.dodecad_through_coordinate
#print axioms Atlas.Codes.mathieu11_to_m23_injective
#print axioms Atlas.Codes.mathieu11_embeddings_commute
#print axioms Atlas.Codes.mathieu11_image_intersection
#print axioms Atlas.Sporadic.Mathieu12.standardDodecad_marked
#print axioms Atlas.Sporadic.Mathieu12.construction_complete
#print axioms Atlas.Sporadic.Mathieu12.exists_model
#print axioms Atlas.Codes.mathieu11_one_point_order
#print axioms Atlas.Codes.mathieu11_two_point_order
#print axioms Atlas.Codes.mathieu11_three_point_order
#print axioms Atlas.Codes.mathieu11_four_point_order
#print axioms Atlas.Codes.mathieu11_not_five_transitive
#print axioms Atlas.Codes.mathieu11Blocks_mem
#print axioms Atlas.Codes.mathieu11Blocks_size
#print axioms Atlas.Codes.mathieu11_steiner
#print axioms Atlas.Codes.mathieu11Blocks_card
#print axioms Atlas.Codes.mathieu11Blocks_preserved
#print axioms Atlas.Codes.mathieu11Blocks_octad_recovery
#print axioms Atlas.Codes.mathieu11Choice_embedding
#print axioms Atlas.Codes.mathieu11Choice_equivariant
#print axioms Atlas.Codes.mathieu11Choice_blocks
#print axioms Atlas.Sporadic.Mathieu11.card
#print axioms Atlas.Sporadic.Mathieu11.isSimpleGroup
#print axioms Atlas.Sporadic.Mathieu11.construction_complete
#print axioms Atlas.Sporadic.Mathieu11.exists_model
#print axioms Atlas.Lattices.leech_lattice_constructed
#print axioms Atlas.Lattices.evenGluingEquiv
#print axioms Atlas.Lattices.oddGluingEquiv
#print axioms Atlas.Lattices.leech_index
#print axioms Atlas.Lattices.leech_gram_determinant
#print axioms Atlas.Lattices.leech_selfDual
#print axioms Atlas.Lattices.leech_minimum
#print axioms Atlas.Lattices.minimal_vectors_span
#print axioms Atlas.Lattices.leech_visible_symmetries_constructed
#print axioms Atlas.Lattices.fullIsometryEquiv
#print axioms Atlas.Lattices.rationalExtension_unique
#print axioms Atlas.Lattices.monomialEmbedding_injective
#print axioms Atlas.Lattices.sign_permutation_compatibility
#print axioms Atlas.Lattices.allOnes_sign_negation
#print axioms Atlas.Lattices.negationIsometry_ne_one
#print axioms Atlas.Lattices.odd_minimal_shell_card
#print axioms Atlas.Lattices.odd_six_shell_card
#print axioms Atlas.Lattices.odd_eight_shell_card
#print axioms Atlas.Lattices.odd_minimal_shell_iff
#print axioms Atlas.Lattices.odd_six_shell_iff
#print axioms Atlas.Lattices.odd_eight_shell_iff
#print axioms Atlas.Lattices.even_minimal_profiles
#print axioms Atlas.Lattices.even_six_profiles
#print axioms Atlas.Lattices.even_eight_profiles
#print axioms Atlas.Lattices.leech_minimal_shell_card
#print axioms Atlas.Lattices.leech_six_shell_card
#print axioms Atlas.Lattices.twoFourFamily_iff
#print axioms Atlas.Lattices.twoFour_shape_counts
#print axioms Atlas.Lattices.pureFour_shape_counts
#print axioms Atlas.Lattices.leech_small_shells_constructed
#print axioms Atlas.Lattices.leech_eight_shell_card
#print axioms Atlas.Lattices.leech_short_shell_counts
#print axioms Atlas.Lattices.sixTwoFamily_iff
#print axioms Atlas.Lattices.normEightTag_card
#print axioms Atlas.Lattices.normEightTag_exhaustive
#print axioms Atlas.Lattices.leech_mod_two_quadratic_constructed
#print axioms Atlas.Lattices.leech_intrinsic_crosses_constructed
#print axioms Atlas.Lattices.leechCross_card
#print axioms Atlas.Lattices.norm_eight_class_capacity
#print axioms Atlas.Lattices.shellClasses_counts
#print axioms Atlas.Lattices.norm_eight_fiber_card
#print axioms Atlas.Lattices.crossRepresentatives_span
#print axioms Atlas.Lattices.standardCross_vectors
#print axioms Atlas.Lattices.leechClassType_counts
#print axioms Atlas.Lattices.leech_constructed
#print axioms Atlas.Lattices.sextetCross_vectors
#print axioms Atlas.Lattices.sextetCross_injective
#print axioms Atlas.Lattices.sextetCrosses_card
#print axioms Atlas.Lattices.sextetSignParity_independent
#print axioms Atlas.Lattices.sextetCross_sign_action
#print axioms Atlas.Lattices.sextetCross_permutation_action
#print axioms Atlas.Conway.monomial_order
#print axioms Atlas.Conway.monomial_fixes_standardCross
#print axioms Atlas.Conway.standardCrossStabilizer_eq_monomial
#print axioms Atlas.Conway.standardCrossStabilizer_order
#print axioms Atlas.Conway.recoverMonomial_spec
#print axioms Atlas.Conway.monomial_stabilizer_constructed
#print axioms Atlas.Conway.sextet_isometry_constructed
#print axioms Atlas.Conway.sextetReflection_lattice
#print axioms Atlas.Conway.zeta_sq
#print axioms Atlas.Conway.zeta_not_monomial
#print axioms Atlas.Conway.zeta_standardCross
#print axioms Atlas.Conway.leech_center_iff
#print axioms Atlas.Conway.central_rational_scalar
#print axioms Atlas.Conway.leechCentralSigns_card
#print axioms Atlas.Conway.leechCentralQuotient_card_relation
#print axioms Atlas.Codes.mathieuSextetRepresentation_injective
#print axioms Atlas.Conway.crossRepresentation_kernel
#print axioms Atlas.Conway.leechModTwoRepresentation_kernel
#print axioms Atlas.Conway.quotientCrossRepresentation_injective
#print axioms Atlas.Conway.quotientModTwoRepresentation_injective
#print axioms Atlas.Conway.quotientModTwoRepresentation_quadratic
#print axioms Atlas.Conway.quotientPermutationEmbedding_injective
#print axioms Atlas.Conway.quotientMonomialEmbedding_kernel
#print axioms Atlas.Conway.quotientMonomialSubgroup_order
#print axioms Atlas.Conway.conway_central_quotient_constructed
#print axioms Atlas.Conway.monomialSignQuotientProjection_kernel
#print axioms Atlas.Conway.quotientMonomialSplitEquiv_compatible
#print axioms Atlas.Conway.quotientMonomialRetraction_splitting
#print axioms Atlas.Conway.quotientMonomialRetraction_kernel
#print axioms Atlas.Conway.golaySignQuotient_card
#print axioms Atlas.Conway.quotientModTwoRepresentation_classType
#print axioms Atlas.Conway.coordinateEight_fixer_mem_monomial
#print axioms Atlas.Conway.leech_prime_order_le
#print axioms Atlas.Conway.minimum_monomial_orbit
#print axioms Atlas.Conway.minimum_monomial_orbit_card
#print axioms Atlas.Conway.leech_forbidden_orbit_sizes
#print axioms Atlas.Conway.orthogonalPairStabilizer_order
#print axioms Atlas.Conway.orthogonalPairStabilizerEquiv_compatible
#print axioms Atlas.Conway.orthogonalPairStabilizer_overgroup_order
#print axioms Atlas.Conway.minimum_monomial_three_orbits
#print axioms Atlas.Conway.odd_point_stabilizer_orbit_dvd
#print axioms Atlas.Conway.minimum_point_cycle_no_orthogonal_fixed_vector
#print axioms Atlas.Conway.orthogonal_five_sizes_fusion
#print axioms Atlas.Codes.mathieu24_marked_octad_transitive
#print axioms Atlas.Codes.mathieu24_pair_fixing_octad_avoiding_transitive
#print axioms Atlas.Conway.golay_octad_exterior_restriction
#print axioms Atlas.Conway.firstShapeStabilizer_eq_monomial
#print axioms Atlas.Conway.strict_overgroup_minimum_pretransitive
#print axioms Atlas.Conway.orthogonalFourClass_card
#print axioms Atlas.Conway.orthogonal_disjoint_four_transitive
#print axioms Atlas.Conway.orthogonal_disjoint_octad_transitive
#print axioms Atlas.Conway.orthogonalClass_monomial_orbit_card
#print axioms Atlas.Conway.orthogonalMinimumShell_card
#print axioms Atlas.Conway.strict_overgroup_orthogonal_orbit_full
#print axioms Atlas.Conway.strict_overgroup_order
#print axioms Atlas.Conway.leechIsometryGroup_order_minimal_pair
#print axioms Atlas.Conway.leechIsometryGroup_order
#print axioms Atlas.Conway.monomial_maximal
#print axioms Atlas.Conway.generatedConwayGroup_eq_full
#print axioms Atlas.Conway.leechCentralQuotient_order
#print axioms Atlas.Conway.full_cross_transitive
#print axioms Atlas.Conway.quotient_cross_primitive
#print axioms Atlas.Conway.quotient_cross_faithful
#print axioms Atlas.Conway.quotient_cross_stabilizer
#print axioms Atlas.Conway.monomial_not_normal
#print axioms Atlas.Conway.octad_sign_mem_commutator
#print axioms Atlas.Conway.monomialDerivedCode_eq_top
#print axioms Atlas.Conway.monomialSubgroup_perfect
#print axioms Atlas.Conway.quotientMonomialSubgroup_perfect
#print axioms Atlas.Conway.four_dimensional_conjugation_identity
#print axioms Atlas.Conway.four_dimensional_conjugation_relabel
#print axioms Atlas.Conway.normalGenerationMonomial_permutation_ne_one
#print axioms Atlas.Conway.golaySign_normalClosure_eq_full
#print axioms Atlas.Conway.leechIsometryGroup_perfect
#print axioms Atlas.Conway.leechCentralQuotient_perfect
#print axioms Atlas.Conway.quotientGolaySignSubgroup_normal
#print axioms Atlas.Conway.quotientGolaySigns_normalClosure_eq_full
#print axioms Atlas.GroupTheory.iwasawa_stabilizer_simple
#print axioms Atlas.Conway.leechCentralQuotient_simple
#print axioms Atlas.Conway.leechCentralQuotient_normal_subgroups
#print axioms Atlas.Conway.leechCentralQuotient_noncommuting_pair
#print axioms Atlas.Conway.leechCentralQuotient_center
#print axioms Atlas.Conway.leechIsometryGroup_not_simple
#print axioms Atlas.Sporadic.Conway1.card
#print axioms Atlas.Sporadic.Conway1.card_factorization
#print axioms Atlas.Sporadic.Conway1.isSimpleGroup
#print axioms Atlas.Sporadic.Conway1.construction
#print axioms Atlas.Sporadic.Conway1.exists_model

#print axioms Atlas.Sporadic.Conway2.card
#print axioms Atlas.Sporadic.Conway2.card_factorization
#print axioms Atlas.Sporadic.Conway2.antipodalStabilizerEquiv
#print axioms Atlas.Sporadic.Conway2.line_index_product
#print axioms Atlas.Sporadic.Conway2.degree
#print axioms Atlas.Sporadic.Conway2.transitive

#print axioms Atlas.Sporadic.Conway2.localSemidirectEquiv
#print axioms Atlas.Sporadic.Conway2.local_card
#print axioms Atlas.Sporadic.Conway2.signs_card
#print axioms Atlas.Sporadic.Conway2.signs_normal
#print axioms Atlas.Sporadic.Conway2.pairProjection_kernel
#print axioms Atlas.Sporadic.Conway2.suborbit_card
#print axioms Atlas.Sporadic.Conway2.primitive

#print axioms Atlas.Conway.marked_short_octads_span

#print axioms Atlas.Conway.marked_short_differences_span
#print axioms Atlas.Conway.co2_short_sign_mem_commutator
#print axioms Atlas.Sporadic.Conway2.exists_mul_ne_mul
#print axioms Atlas.Sporadic.Conway2.connector_sq
#print axioms Atlas.Sporadic.Conway2.connector_outside_local

#print axioms Atlas.Sporadic.Conway2.outerPairSection_rightInverse
#print axioms Atlas.Conway.co2Pair_normal_eq_top
#print axioms Atlas.Sporadic.Conway2.signs_normalClosure
#print axioms Atlas.Sporadic.Conway2.perfect

#print axioms Atlas.Sporadic.Conway2.faithful
#print axioms Atlas.Sporadic.Conway2.isSimpleGroup

#print axioms Atlas.Sporadic.Conway2.complement_rank
#print axioms Atlas.Sporadic.Conway2.integralRepresentation_injective
#print axioms Atlas.Sporadic.Conway2.construction
#print axioms Atlas.Sporadic.Conway2.exists_model

#print axioms Atlas.Sporadic.Conway3.vector_norm
#print axioms Atlas.Sporadic.Conway3.mathieu23Embedding_injective
#print axioms Atlas.Sporadic.Conway3.toConway1_injective
#print axioms Atlas.Sporadic.Conway3.complement_rank
#print axioms Atlas.Sporadic.Conway3.integralRepresentation_injective
#print axioms Atlas.Conway.normSix_point_decomposition
#print axioms Atlas.Conway.co3_base_triangle_norms

#print axioms Atlas.Sporadic.Conway3.card
#print axioms Atlas.Sporadic.Conway3.card_factorization
#print axioms Atlas.Sporadic.Conway3.shell_transitive
#print axioms Atlas.Sporadic.Conway3.line_index

#print axioms Atlas.Sporadic.Conway3.degree
#print axioms Atlas.Sporadic.Conway3.faithful
#print axioms Atlas.Sporadic.Conway3.pointHeptad_equivariant
#print axioms Atlas.Sporadic.Conway3.triangleMathieuEquiv
#print axioms Atlas.Sporadic.Conway3.exists_mul_ne_mul

#print axioms Atlas.Sporadic.Conway3.two_transitive
#print axioms Atlas.Sporadic.Conway3.primitive
#print axioms Atlas.Sporadic.Conway3.point_stabilizer_card
#print axioms Atlas.Conway.co3LocalType_card
#print axioms Atlas.Codes.mathieu23_heptad_intersection_one_card
#print axioms Atlas.Sporadic.Conway3.triangles_card
#print axioms Atlas.Sporadic.Conway3.triangle_shape_card
#print axioms Atlas.Sporadic.Conway3.triangle_stabilizer_eq
#print axioms Atlas.Sporadic.Conway3.triangle_subdegree
#print axioms Atlas.Sporadic.Conway3.triangle_mathieu_orbits
#print axioms Atlas.Sporadic.Conway3.triangles_transitive
#print axioms Atlas.Sporadic.Conway3.triangles_primitive
#print axioms Atlas.Sporadic.Conway3.triangle_stabilizer_maximal
#print axioms Atlas.Conway.co3_sylow23_card
#print axioms Atlas.Conway.co3_normal_contains_mathieu
#print axioms Atlas.Sporadic.Conway3.isSimpleGroup
#print axioms Atlas.Sporadic.Conway3.construction
#print axioms Atlas.Sporadic.Conway3.construction_complete
#print axioms Atlas.Sporadic.Conway3.exists_model
#print axioms Atlas.Sporadic.Conway3.mathieu23Embedding_range
#print axioms Atlas.Sporadic.Conway3.antipodalStabilizerEquiv_compatible
#print axioms Atlas.Sporadic.McLaughlin.card
#print axioms Atlas.Sporadic.McLaughlin.endpointPermutation_surjective
#print axioms Atlas.Sporadic.McLaughlin.toPairStabilizer_range
#print axioms Atlas.Conway.mcl_endpoint_not_fixed
#print axioms Atlas.Sporadic.McLaughlin.degree
#print axioms Atlas.Sporadic.McLaughlin.transitive
#print axioms Atlas.Sporadic.McLaughlin.faithful
#print axioms Atlas.Sporadic.McLaughlin.strongly_regular
#print axioms Atlas.Sporadic.McLaughlin.point_family_orbit
#print axioms Atlas.Sporadic.McLaughlin.point_labels_primitive
#print axioms Atlas.Sporadic.McLaughlin.exists_mul_ne_mul
#print axioms Atlas.Sporadic.McLaughlin.triangle_degree
#print axioms Atlas.Sporadic.McLaughlin.triangles_primitive
#print axioms Atlas.Sporadic.McLaughlin.triangles_faithful
#print axioms Atlas.Sporadic.McLaughlin.triangle_stabilizer_maximal
#print axioms Atlas.Sporadic.McLaughlin.isSimpleGroup
#print axioms Atlas.Sporadic.McLaughlin.perfect
#print axioms Atlas.Sporadic.McLaughlin.pair_commutator_eq_kernel
#print axioms Atlas.Sporadic.McLaughlin.complement_rank
#print axioms Atlas.Sporadic.McLaughlin.integralRepresentation_injective
#print axioms Atlas.Sporadic.McLaughlin.toConway2_compatible
#print axioms Atlas.Sporadic.McLaughlin.construction
#print axioms Atlas.Sporadic.McLaughlin.exists_model
#print axioms Atlas.Sporadic.HigmanSims.sides_card
#print axioms Atlas.Sporadic.HigmanSims.degree
#print axioms Atlas.Sporadic.HigmanSims.strongly_regular
#print axioms Atlas.Sporadic.HigmanSims.connected
#print axioms Atlas.Sporadic.HigmanSims.point_stabilizer_card
#print axioms Atlas.Sporadic.HigmanSims.point_stabilizer_simple
#print axioms Atlas.Sporadic.HigmanSims.faithful
#print axioms Atlas.Sporadic.HigmanSims.local_fiber_card
#print axioms Atlas.Sporadic.HigmanSims.card
#print axioms Atlas.Sporadic.HigmanSims.saturated_orbit_bounds
#print axioms Atlas.Sporadic.HigmanSims.sides_transitive
#print axioms Atlas.Sporadic.HigmanSims.transitive
#print axioms Atlas.Sporadic.HigmanSims.rank_three
#print axioms Atlas.Sporadic.HigmanSims.primitive
#print axioms Atlas.Sporadic.HigmanSims.regular_normal_impossible
#print axioms Atlas.Sporadic.HigmanSims.isSimpleGroup
#print axioms Atlas.Sporadic.HigmanSims.perfect
#print axioms Atlas.Sporadic.HigmanSims.complement_rank
#print axioms Atlas.Sporadic.HigmanSims.integralRepresentation_injective
#print axioms Atlas.Sporadic.HigmanSims.toConway2_compatible
#print axioms Atlas.Sporadic.HigmanSims.decomposition_complement_card
#print axioms Atlas.Sporadic.HigmanSims.construction
#print axioms Atlas.Sporadic.HigmanSims.exists_model

#print axioms Atlas.Codes.ternaryGolay_selfDual
#print axioms Atlas.Codes.ternaryGolay_weight_distribution
#print axioms Atlas.Codes.ternaryGolay_minimum
#print axioms Atlas.Codes.ternaryPhaseModule_finrank
#print axioms Atlas.Algebra.eisenstein_units_card
#print axioms Atlas.Algebra.eisensteinResidueEquiv
#print axioms Atlas.Lattices.eisensteinCongruence_lift_independent
#print axioms Atlas.Lattices.eisensteinLeechModule
#print axioms Atlas.Lattices.eisensteinLeechModule_coordinate_frame
#print axioms Atlas.Codes.ternaryHexads_count
#print axioms Atlas.Codes.ternaryHexads_steiner
#print axioms Atlas.Codes.ternarySixSupport_fiber
#print axioms Atlas.Codes.ternaryBinaryLiftBasis_eq
#print axioms Atlas.Codes.ternaryBinaryOctadLift_spec
#print axioms Atlas.Codes.ternaryWitt_hexads_iff
#print axioms Atlas.Codes.ternaryWittMathieuHom_injective
#print axioms Atlas.Codes.ternaryWittMathieu_sharp_five

/-! ## Eisenstein scalar and actual ternary Mathieu comparison -/
#print axioms Atlas.Algebra.eisensteinToRational_injective
#print axioms Atlas.Algebra.eisensteinReal_ext
#print axioms Atlas.Lattices.eisensteinHermitian_of_real_and_rotation
#print axioms Atlas.Lattices.eisensteinLinear_of_rotation
#print axioms Atlas.Lattices.eisensteinBilinear_self_eq_zero
#print axioms Atlas.Lattices.eisensteinRotationEquiv_order
#print axioms Atlas.Lattices.rationalEisensteinLattice_full_span
#print axioms Atlas.Lattices.rationalEisensteinCoordinates_finrank
#print axioms Atlas.Lattices.eisensteinLeechModule_eq_integral_span
#print axioms Atlas.Lattices.eisensteinComparison_isometry
#print axioms Atlas.Lattices.eisensteinComparison_forward
#print axioms Atlas.Lattices.eisensteinComparison_reverse
#print axioms Atlas.Lattices.eisensteinComparison_lattice_iff
#print axioms Atlas.Conway.eisensteinRho_polynomial
#print axioms Atlas.Conway.eisensteinRho_fixed_iff
#print axioms Atlas.Conway.eisensteinRho_order
#print axioms Atlas.Codes.ternaryFullWords_card
#print axioms Atlas.Codes.ternaryFullPairs_card
#print axioms Atlas.Codes.ternaryFullPairs_orthogonal
#print axioms Atlas.Codes.ternaryDiagonal_automorphism_scalars
#print axioms Atlas.Codes.ternarySigned_lift_unique
#print axioms Atlas.Codes.ternaryPureMathieu11Equiv
#print axioms Atlas.Codes.ternaryPureAutomorphism_order
#print axioms Atlas.Codes.ternaryPureAutomorphism_simple
#print axioms Atlas.Codes.ternaryPhase_fixed_eq_zero
#print axioms Atlas.RepresentationTheory.ternary_finrank_five_invariant_eq_bot_or_top
#print axioms Atlas.RepresentationTheory.difference_surjective_of_fixed_eq_zero
#print axioms Atlas.GroupTheory.semidirect_isPerfect_of_action_differences
#print axioms Atlas.Conway.eisensteinHermitianToCo0_range
#print axioms Atlas.Conway.eisensteinCentralizerEquiv
#print axioms Atlas.Conway.eisensteinCentralizerEquiv_agrees
#print axioms Atlas.Lattices.eisensteinLeech_rank
#print axioms Atlas.Lattices.eisensteinTheta_quotient_card
#print axioms Atlas.Lattices.eisensteinShell_four_card
#print axioms Atlas.Lattices.eisensteinShell_six_card
#print axioms Atlas.Lattices.eisensteinNorm_minimum
#print axioms Atlas.Lattices.eisensteinNorm_theta_minimum
#print axioms Atlas.Lattices.eisenstein_four_class_card
#print axioms Atlas.Lattices.eisenstein_four_six_differentClass
#print axioms Atlas.Lattices.eisenstein_six_class_card_le
#print axioms Atlas.Lattices.eisensteinShellClasses_counts
#print axioms Atlas.Lattices.eisensteinShortClasses_eq_univ
#print axioms Atlas.Lattices.eisenstein_six_class_card
#print axioms Atlas.Lattices.eisenstein_six_scalar_integral_unit
#print axioms Atlas.Lattices.eisenstein_six_line_card
#print axioms Atlas.Lattices.eisensteinFrame_card
#print axioms Atlas.Lattices.eisensteinFrameVectors_card
#print axioms Atlas.Lattices.eisensteinFrameVectors_injective
#print axioms Atlas.Conway.eisensteinFullFrameStabilizer_order
#print axioms Atlas.Conway.eisensteinFullFrameGroupEquiv
#print axioms Atlas.Conway.eisensteinFrameToCo0_agrees
#print axioms Atlas.Conway.eisensteinFrameModuloScalarsEquiv
#print axioms Atlas.Conway.eisensteinFrameModuloScalars_order
#print axioms Atlas.Conway.eisensteinFrameModuloScalars_perfect
#print axioms Atlas.Conway.eisensteinScalarSubgroup_order
#print axioms Atlas.Conway.eisensteinCentralizerScalars_order
#print axioms Atlas.Conway.eisensteinCentralizerScalars_le_center
#print axioms Atlas.Conway.eisensteinUnitIsometries_Co0_agrees
#print axioms Atlas.Conway.eisensteinFrameScalarSubgroup_comap
#print axioms Atlas.Conway.eisensteinIntegralAction_agrees
#print axioms Atlas.Conway.eisensteinIntegralAction_scalar
#print axioms Atlas.Conway.eisensteinFrameAction_vector
#print axioms Atlas.Conway.eisensteinFrameAction_vectors
#print axioms Atlas.Conway.eisensteinProjectiveComparison
#print axioms Atlas.Codes.ternaryPhase_invariant_eq_bot_or_top
#print axioms Atlas.Codes.ternaryPurePhaseLinearHom_injective
#print axioms Atlas.Codes.ternaryLocalPhaseGroup_perfect
#print axioms Atlas.Codes.ternaryLocalPhase_centralizer
#print axioms Atlas.Codes.ternaryLocalPhase_normal_subgroups
#print axioms Atlas.Lattices.eisensteinScalarLine_finrank
#print axioms Atlas.Lattices.eisensteinFrameLines_card
#print axioms Atlas.Lattices.eisensteinFrameLines_recovers_vectors
#print axioms Atlas.Lattices.eisensteinFrameLines_injective
#print axioms Atlas.Lattices.eisensteinFrameLines_orthogonal
#print axioms Atlas.Conway.eisensteinStandardFrame_vectors
#print axioms Atlas.Conway.eisensteinStandardFrame_stabilizer
#print axioms Atlas.Conway.eisensteinStandardFrame_stabilizer_order
#print axioms Atlas.Conway.eisensteinUnitIsometries_frame
#print axioms Atlas.Conway.eisensteinScalarSubgroup_frame_kernel
#print axioms Atlas.Conway.eisensteinProjectiveFrameAction_mk
#print axioms Atlas.Lattices.eisensteinFrameLines_span
#print axioms Atlas.Lattices.eisensteinFrameLines_ext

-- Suz local geometry and scalar quotient; global order and simplicity remain separate.
#print axioms Atlas.Lattices.eisensteinTriadFamily_card
#print axioms Atlas.Conway.eisensteinTriadFamily_transitive
#print axioms Atlas.Conway.eisensteinTriadFamily_orbit
#print axioms Atlas.Conway.eisensteinFourier_standard_triad
#print axioms Atlas.Conway.eisensteinFourier_standard_mem_triad
#print axioms Atlas.Lattices.eisensteinTriadFrame_eq_iff
#print axioms Atlas.Lattices.eisensteinClass_difference_three_iff
#print axioms Atlas.Conway.eisensteinBalancedFamily_card
#print axioms Atlas.Conway.eisensteinBalancedFamily_orbit
#print axioms Atlas.Conway.eisensteinBalancedFamily_transitive
#print axioms Atlas.Conway.eisensteinBalancedClass_eq_iff
#print axioms Atlas.Conway.eisensteinBalancedParameterClass_fiber_card
#print axioms Atlas.Codes.ternaryHexadRestriction_range
#print axioms Atlas.Codes.ternaryHexadConstantCode_card
#print axioms Atlas.Conway.eisensteinFourier_triad_balanced
#print axioms Atlas.Algebra.eisenstein_small_norm_unit
#print axioms Atlas.Conway.eisensteinHeavyUnitFrame_eq_iff
#print axioms Atlas.Conway.eisensteinHeavyUnitFramesEquiv
#print axioms Atlas.Conway.eisensteinHeavyUnitFrames_card
#print axioms Atlas.Conway.eisensteinHeavyUnitFrames_orbit
#print axioms Atlas.Conway.eisensteinHeavyUnitOrbit_card
#print axioms Atlas.Conway.eisensteinHeavyUnitFrames_transitive
#print axioms Atlas.Conway.eisensteinHeavyUnitFrames_iff
#print axioms Atlas.Lattices.eisensteinResidueOne_normalize
#print axioms Atlas.Conway.eisensteinOneModThree_class_iff
#print axioms Atlas.Conway.eisensteinOneModThree_frame_phase_iff
#print axioms Atlas.Conway.eisensteinPairUnitFrame_eq_iff
#print axioms Atlas.Conway.eisensteinPairUnitFramesEquiv
#print axioms Atlas.Conway.eisensteinPairUnitFrames_card
#print axioms Atlas.Conway.eisensteinPairUnitFrames_disjoint
#print axioms Atlas.Conway.eisensteinPairUnitFrames_orbit
#print axioms Atlas.Conway.eisensteinPairUnitOrbit_card
#print axioms Atlas.Conway.eisensteinPairUnitFrames_iff
#print axioms Atlas.Lattices.eisenstein_scalar_norm_le27
#print axioms Atlas.Lattices.eisenstein_six_zeroResidue_weight
#print axioms Atlas.Lattices.eisenstein_six_zeroResidue_patterns
#print axioms Atlas.Lattices.eisenstein_six_nonzeroResidue_patterns
#print axioms Atlas.Lattices.eisenstein_six_residue_dichotomy
#print axioms Atlas.Conway.eisensteinProjectiveFrame_kernel
#print axioms Atlas.Conway.eisensteinProjectiveFrame_faithful
#print axioms Atlas.Conway.eisensteinTripleToCo1_injective
#print axioms Atlas.Conway.eisensteinTripleProjection_kernel_card
#print axioms Atlas.Conway.eisensteinTripleProjection_kernel_central
#print axioms Atlas.Conway.eisensteinHermitianFrame_kernel
#print axioms Atlas.Conway.eisensteinLocalProjectiveEmbedding_injective
#print axioms Atlas.Conway.eisensteinLocalProjectiveEmbedding_range
#print axioms Atlas.Conway.eisensteinProjective_fusion
#print axioms Atlas.Conway.eisensteinProjectivePhases_card
#print axioms Atlas.Conway.eisensteinProjectivePhases_abelian
#print axioms Atlas.Conway.eisensteinLocal_le_phase_normalClosure
#print axioms Atlas.Conway.eisensteinTripleToCo1_mk
#print axioms Atlas.Conway.eisensteinTripleProjection_surjective
#print axioms Atlas.Conway.eisensteinTripleProjection_kernel
#print axioms Atlas.Conway.eisenstein_subdegree_block_arithmetic
#print axioms Atlas.GroupTheory.normal_eq_top_of_full_stabilizer
#print axioms Atlas.GroupTheory.perfect_of_perfect_stabilizer
#print axioms Atlas.Conway.eisensteinShortSingleton_norm
#print axioms Atlas.Conway.eisensteinShortPair_norm
#print axioms Atlas.Conway.eisensteinOneModThree_short_excluded
#print axioms Atlas.Codes.ternaryConstantHexadPairs_transitive
#print axioms Atlas.Lattices.eisensteinHexadFrame_lines
#print axioms Atlas.Conway.eisensteinHexadFrame_phase_stabilizer
#print axioms Atlas.Conway.eisensteinHexadPhaseOrbit_card
#print axioms Atlas.Conway.eisensteinHexadFamily_card
#print axioms Atlas.Conway.eisensteinHexadFamily_transitive
#print axioms Atlas.Conway.eisensteinHexadFamily_preserved
#print axioms Atlas.Conway.eisensteinHexadFamily_orbit
#print axioms Atlas.Conway.eisensteinNine_frame_phase_kernel
#print axioms Atlas.Conway.eisensteinNine_phase_stabilizer_card
#print axioms Atlas.Conway.eisensteinNine_phase_orbit_card
#print axioms Atlas.Lattices.eisensteinClass_coordinateResidue
#print axioms Atlas.Lattices.eisensteinZeroResidue_frame
#print axioms Atlas.Lattices.eisenstein_six_normalized_weight
#print axioms Atlas.Lattices.eisenstein_constant_hexad_class_normalized
#print axioms Atlas.Conway.eisensteinLocalNormCount
#print axioms Atlas.Codes.ternaryOrientedSyndromes_card
#print axioms Atlas.Codes.ternarySyndrome_partition
#print axioms Atlas.Codes.ternaryOrientedSyndrome_fiber_card
#print axioms Atlas.Codes.ternaryOrientedSyndromes_orbit

-- Suz local geometry and scalar quotient; global order and simplicity remain separate.
#print axioms Atlas.Conway.eisensteinTriadUnit_norm
#print axioms Atlas.Conway.eisensteinTriadUnit_class_iff
#print axioms Atlas.Conway.eisensteinTriadUnitFrame_eq_iff
#print axioms Atlas.Conway.eisensteinTriadUnitFramesEquiv
#print axioms Atlas.Conway.eisensteinTriadUnitFrames_card
#print axioms Atlas.Conway.eisensteinTriadUnitFrames_disjoint
#print axioms Atlas.Conway.eisensteinTriadUnitFrames_orbit
#print axioms Atlas.Conway.eisensteinTriadUnitOrbit_card
#print axioms Atlas.Conway.eisensteinOneModThree_frame_syndrome
#print axioms Atlas.Conway.eisensteinHeavy_pair_disjoint
#print axioms Atlas.Conway.eisensteinHeavy_triad_disjoint
#print axioms Atlas.Conway.eisensteinPair_triad_disjoint
#print axioms Atlas.Conway.eisensteinUnitResidue_normalize
#print axioms Atlas.Conway.eisensteinBalancedProfile_exhaustion
#print axioms Atlas.Conway.eisensteinBalancedFrame_pattern

-- Suz full scalar-centralizer generation and order; simplicity is a later checkpoint.
#print axioms Atlas.Lattices.eisensteinBalancedNineVectors_card
#print axioms Atlas.Conway.eisensteinBalancedNineVectors_transitive
#print axioms Atlas.Conway.eisensteinBalancedNineFamily_card
#print axioms Atlas.Conway.eisensteinBalancedNineFamily_transitive
#print axioms Atlas.Conway.eisensteinBalancedNineFamily_invariant
#print axioms Atlas.Conway.eisensteinBalancedNineFamily_orbit
#print axioms Atlas.Conway.eisensteinNineBridgeFrameFiber_card
#print axioms Atlas.Conway.eisensteinBalancedNineFamily_Fourier_edge
#print axioms Atlas.Conway.eisensteinBalancedNineFrame_pattern
#print axioms Atlas.Algebra.eisenstein_residue_one_mod_three
#print axioms Atlas.Conway.eisensteinOneModThree_affine_sum
#print axioms Atlas.Conway.eisensteinOneModThree_singleton_frame
#print axioms Atlas.Conway.eisensteinOneModThree_pair_frame
#print axioms Atlas.Conway.eisensteinOneModThree_triad_frame
#print axioms Atlas.Conway.eisensteinNonzeroResidue_frame_exhaust
#print axioms Atlas.Conway.eisensteinUnitResidueFrames_card
#print axioms Atlas.Conway.eisensteinUnitResidueFrames_iff
#print axioms Atlas.Conway.eisensteinFrame_unitResidue_iff
#print axioms Atlas.Conway.eisensteinZeroResidueFrames_card
#print axioms Atlas.GroupTheory.normal_orbit_card_dvd
#print axioms Atlas.GroupTheory.orbit_families_disjoint_of_card_ne
#print axioms Atlas.GroupTheory.orbit_families_pairwise_disjoint_of_degrees
#print axioms Atlas.Conway.eisensteinPhase_orbit_card_dvd_local
#print axioms Atlas.Conway.eisensteinNineHexadFamily_phase_card
#print axioms Atlas.Conway.eisensteinNineHexadFamily_unit_disjoint
#print axioms Atlas.Conway.eisensteinNineHexadFamily_other_disjoint
#print axioms Atlas.Conway.eisensteinNineSignFrame_not_other
#print axioms Atlas.Conway.eisensteinNineHexadFamily_preserved
#print axioms Atlas.Conway.eisensteinNineHexadFamily_transitive
#print axioms Atlas.Conway.eisensteinNineHexadFamily_orbit
#print axioms Atlas.Conway.eisensteinNineHexadFamily_card
#print axioms Atlas.Conway.eisensteinNineHexadFamily_disjoint
#print axioms Atlas.Conway.eisensteinNineHexadFamily_mem_iff_sign
#print axioms Atlas.Conway.eisensteinNineHexadFrame_mem_family
#print axioms Atlas.Conway.eisensteinNineSignFrame_preserved
#print axioms Atlas.Conway.eisensteinNineSignFrame_unique
#print axioms Atlas.Conway.eisensteinNineHexadPhaseOrbit_card
#print axioms Atlas.Conway.eisensteinNineHexadFrame_phase_sign
#print axioms Atlas.Conway.eisensteinNineHexadFrame_phase_partition
#print axioms Atlas.Conway.eisensteinConstantNineParameters_card
#print axioms Atlas.Conway.eisensteinConstantNineParameterVector_mem
#print axioms Atlas.Conway.eisensteinConstantNineParameter_norm
#print axioms Atlas.Conway.eisensteinConstantNineParameterVector_injective
#print axioms Atlas.Conway.eisensteinConstantNine_normal_form
#print axioms Atlas.Conway.eisensteinHexad_normalized_code_phase
#print axioms Atlas.Conway.eisensteinHexad_normalized_frame
#print axioms Atlas.Conway.eisensteinHexad_normalized_excludes_nine
#print axioms Atlas.Conway.eisenstein_constant_frame_norm9_pattern
#print axioms Atlas.Lattices.eisenstein_constant_normalized_norm_pattern
#print axioms Atlas.Lattices.eisensteinLeech_constant_hexad_sum
#print axioms Atlas.Lattices.eisensteinTheta_frame_difference
#print axioms Atlas.Conway.eisensteinConstantNine_frame_sign_same
#print axioms Atlas.Conway.eisensteinConstantNine_frame_sign_compl
#print axioms Atlas.Conway.eisensteinNineHexadFrame_sign
#print axioms Atlas.Conway.eisensteinNineHexadFamily_sign
#print axioms Atlas.Conway.eisensteinNineSignFrame_phase_orbit_card
#print axioms Atlas.Conway.eisensteinHexadFamily_disjoint_nine
#print axioms Atlas.Conway.eisensteinSuborbitFrames_card
#print axioms Atlas.Conway.eisensteinSuborbitFrames_orbit
#print axioms Atlas.Conway.eisensteinSuborbitFrames_transitive
#print axioms Atlas.Conway.eisensteinSuborbitFrames_pairwise
#print axioms Atlas.Conway.eisensteinSuborbitFrames_cover
#print axioms Atlas.Conway.eisensteinNineHexadUnion_invariant
#print axioms Atlas.Conway.eisensteinFourier_heavy_balanced
#print axioms Atlas.Conway.eisensteinFourier_pair_balanced
#print axioms Atlas.Conway.eisensteinFourier_unitTriad_balanced
#print axioms Atlas.Conway.eisensteinFourier_hexad_triad
#print axioms Atlas.Conway.eisensteinFourier_constantNine_mem_unit
#print axioms Atlas.Conway.eisensteinGeneratedFrames_all
#print axioms Atlas.Conway.eisensteinGeneratedGroup_eq_top
#print axioms Atlas.Conway.eisensteinHermitian_frame_transitive
#print axioms Atlas.Conway.eisensteinHermitian_order
#print axioms Atlas.Conway.eisensteinCentralizer_order
#print axioms Atlas.Conway.eisensteinHermitian_frame_order_identity
#print axioms Atlas.Conway.eisensteinCentralizer_scalar_order_identity
#print axioms Atlas.Conway.eisensteinCentralizer_six_dvd
#print axioms Atlas.Conway.eisensteinProjective_order
#print axioms Atlas.Conway.eisensteinProjective_order_factorization
#print axioms Atlas.Conway.eisensteinHermitianQuotient_order
#print axioms Atlas.GroupTheory.finite_families_cover_of_card_sum

-- Job 19 S4-S6: unconditional simplicity and complete public Suzuki package.
#print axioms Atlas.Sporadic.Suzuki.finite
#print axioms Atlas.Sporadic.Suzuki.card
#print axioms Atlas.Sporadic.Suzuki.order
#print axioms Atlas.Sporadic.Suzuki.linear_card
#print axioms Atlas.Sporadic.Suzuki.isSimpleGroup
#print axioms Atlas.Sporadic.Suzuki.nonabelian
#print axioms Atlas.Sporadic.Suzuki.exists_mul_ne_mul
#print axioms Atlas.Sporadic.Suzuki.perfect
#print axioms Atlas.Sporadic.Suzuki.embedding_injective
#print axioms Atlas.Sporadic.Suzuki.projection_surjective
#print axioms Atlas.Sporadic.Suzuki.tripleToConway1_injective
#print axioms Atlas.Sporadic.Suzuki.tripleProjection_surjective
#print axioms Atlas.Sporadic.Suzuki.tripleProjection_kernel_card
#print axioms Atlas.Sporadic.Suzuki.tripleProjection_kernel_central
#print axioms Atlas.Sporadic.Suzuki.tripleToConway1_compatible
#print axioms Atlas.Sporadic.Suzuki.center
#print axioms Atlas.Sporadic.Suzuki.center_card
#print axioms Atlas.Sporadic.Suzuki.triple_card
#print axioms Atlas.Sporadic.Suzuki.lattice_comparison_onto
#print axioms Atlas.Sporadic.Suzuki.lattice_comparison_isometry
#print axioms Atlas.Sporadic.Suzuki.integral_rank
#print axioms Atlas.Sporadic.Suzuki.scalar_rank
#print axioms Atlas.Sporadic.Suzuki.rational_scalar_rank
#print axioms Atlas.Sporadic.Suzuki.scalar_finite
#print axioms Atlas.Sporadic.Suzuki.integral_free
#print axioms Atlas.Sporadic.Suzuki.integral_finite
#print axioms Atlas.Sporadic.Suzuki.rotation_order
#print axioms Atlas.Sporadic.Suzuki.rotation_fixed_iff
#print axioms Atlas.Sporadic.Suzuki.rotation_polynomial
#print axioms Atlas.Sporadic.Suzuki.full_centralizer
#print axioms Atlas.Sporadic.Suzuki.linear_comparison_compatible
#print axioms Atlas.Sporadic.Suzuki.linear_faithful
#print axioms Atlas.Sporadic.Suzuki.linear_scalar_linear
#print axioms Atlas.Sporadic.Suzuki.linear_hermitian
#print axioms Atlas.Sporadic.Suzuki.linear_lattice
#print axioms Atlas.Sporadic.Suzuki.degree
#print axioms Atlas.Sporadic.Suzuki.faithful
#print axioms Atlas.Sporadic.Suzuki.primitive
#print axioms Atlas.Sporadic.Suzuki.transitive
#print axioms Atlas.Sporadic.Suzuki.full_frame_stabilizer
#print axioms Atlas.Sporadic.Suzuki.frame_stabilizer_card
#print axioms Atlas.Sporadic.Suzuki.frame_stabilizer_maximal
#print axioms Atlas.Sporadic.Suzuki.local_card
#print axioms Atlas.Sporadic.Suzuki.suborbit_card
#print axioms Atlas.Sporadic.Suzuki.suborbit_cover
#print axioms Atlas.Sporadic.Suzuki.suborbit_disjoint
#print axioms Atlas.Sporadic.Suzuki.suborbit_pairwise
#print axioms Atlas.Sporadic.Suzuki.localEmbedding_range
#print axioms Atlas.Sporadic.Suzuki.local_orbit_correspondence
#print axioms Atlas.Sporadic.Suzuki.suborbit_transitive
#print axioms Atlas.Sporadic.Suzuki.suborbit_is_orbit
#print axioms Atlas.Sporadic.Suzuki.phase_normal_generation
#print axioms Atlas.Sporadic.Suzuki.linear_frame_kernel
#print axioms Atlas.Sporadic.Suzuki.monomial_fourier_generation
#print axioms Atlas.Sporadic.Suzuki.phase_fourier_fusion
#print axioms Atlas.Sporadic.Suzuki.theta_quotient_card
#print axioms Atlas.Sporadic.Suzuki.construction
#print axioms Atlas.Sporadic.Suzuki.construction_complete
#print axioms Atlas.Sporadic.Suzuki.exists_model
#print axioms Atlas.Conway.eisensteinHermitian_frame_primitive
#print axioms Atlas.Conway.eisensteinProjective_frame_primitive
#print axioms Atlas.Conway.eisensteinPhase_normalClosure
#print axioms Atlas.Conway.eisensteinProjective_perfect
#print axioms Atlas.Conway.eisensteinProjective_simple
#print axioms Atlas.Conway.eisensteinProjective_nonabelian
#print axioms Atlas.Conway.eisensteinFourier_fusion
#print axioms Atlas.Conway.eisensteinFusionInput_phase_ne_zero
#print axioms Atlas.Codes.ternaryPhase_action_difference_surjective
#print axioms Atlas.Conway.eisensteinProjectiveFusionInput_mem
#print axioms Atlas.Conway.eisensteinProjectiveFusionOutput_not_mem
#print axioms Atlas.Sporadic.Suzuki.projective_frame_stabilizer_maximal
#print axioms Atlas.Sporadic.Suzuki.projective_frame_stabilizer_not_normal

-- Job20 scalar and finite-glue checkpoint.
#print axioms Atlas.Algebra.goldenFunctional_weighted_trace
#print axioms Atlas.Algebra.goldenFunctional_sq_eq_zero
#print axioms Atlas.Algebra.icosianFunctional_pairing_ext
#print axioms Atlas.Algebra.icosianOrder_eq_generated
#print axioms Atlas.Algebra.icosianOrder_rank
#print axioms Atlas.Algebra.icosianOrder_star_mem
#print axioms Atlas.Algebra.goldenFour_card
#print axioms Atlas.Algebra.icosianModuloTwo_surjective
#print axioms Atlas.Algebra.icosianModuloTwo_eq_zero_iff_two_mul
#print axioms Atlas.Algebra.icosianTwiceIdeal_mem
#print axioms Atlas.Algebra.icosianModuloTwoQuotient_mk
#print axioms Atlas.Algebra.icosianP_ne_PZero
#print axioms Atlas.Algebra.icosianP_intersection
#print axioms Atlas.Algebra.icosianP_maximal
#print axioms Atlas.Algebra.icosianPZero_maximal
#print axioms Atlas.Algebra.icosianModuloTwo_of_coefficients
#print axioms Atlas.Algebra.icosianParityIntegral_double
#print axioms Atlas.Algebra.icosianParityIntegral_synthesis
#print axioms Atlas.Algebra.isIcosian_coordinates_of_parity
#print axioms Atlas.Algebra.icosianShortCoordinates_parity
#print axioms Atlas.Algebra.icosianNormOneGroup_card
#print axioms Atlas.Algebra.icosianNorm_eq_zero
#print axioms Atlas.Algebra.icosianQuaternion_divisionRing
#print axioms Atlas.Algebra.icosianOrder_goldenRank
#print axioms Atlas.Algebra.icosianOrder_golden_smul
#print axioms Atlas.Algebra.icosianIntegralNorm_spec
#print axioms Atlas.Algebra.icosianModuloTwo_det
#print axioms Atlas.Algebra.icosianNormOneReduction
#print axioms Atlas.Algebra.icosianNormOneReduction_kernel_values
#print axioms Atlas.Algebra.icosianNormOneReduction_kernel_card
#print axioms Atlas.Algebra.goldenFour_SL_card
#print axioms Atlas.Algebra.icosianNormOneReduction_surjective
#print axioms Atlas.Algebra.icosianModuloTwo_star
#print axioms Atlas.Codes.icosianGlue_coefficients
#print axioms Atlas.Codes.icosianGlue_preserves_iff
#print axioms Atlas.Codes.icosianGlueBlockParameterEquiv
#print axioms Atlas.Codes.icosianGlueBlockStabilizer_card_four
#print axioms Atlas.Codes.icosianGlueMonomialStabilizer_iff
#print axioms Atlas.Codes.icosianGlueMonomialStabilizerEquiv
#print axioms Atlas.Codes.icosianGlueMonomialStabilizer_card_four
#print axioms Atlas.Codes.icosianGlueLinearEquiv
#print axioms Atlas.Codes.icosianGlue_finrank
#print axioms Atlas.Codes.icosianGlue_card_four
#print axioms Atlas.Codes.icosianMatrixGlue_constraints
#print axioms Atlas.Codes.icosianMatrixGlue_reconstruct
#print axioms Atlas.Codes.icosianMatrixGlueLinearEquiv
#print axioms Atlas.Codes.icosianMatrixGlue_finrank
#print axioms Atlas.Codes.icosianMatrixGlue_card_four
#print axioms Atlas.Codes.icosianMatrixGlue_right_mem
#print axioms Atlas.Codes.icosianMatrixGlue_column_smul
#print axioms Atlas.Codes.icosianMatrixGlue_stabilizes_iff
#print axioms Atlas.Codes.icosianMatrixGlueMonomialStabilizer_eq
#print axioms Atlas.Codes.icosianMatrixGlueMonomialStabilizer_card_four

-- Job20 actual lattice comparison, full centralizer and reflections.
#print axioms Atlas.Lattices.icosianBilinear_eq_dot
#print axioms Atlas.Lattices.icosianComparison_matrix_inverse
#print axioms Atlas.Lattices.icosianComparison_inverse_matrix
#print axioms Atlas.Lattices.icosianComparison_matrix_gram
#print axioms Atlas.Lattices.icosianComparison_isometry
#print axioms Atlas.Lattices.icosianComparisonSourceGenerator_mem
#print axioms Atlas.Lattices.icosianComparison_generator_check
#print axioms Atlas.Lattices.icosianComparisonPreimage_mem
#print axioms Atlas.Lattices.icosianComparison_preimage_check
#print axioms Atlas.Lattices.icosianLeechModule_le_of_generators
#print axioms Atlas.Lattices.icosianComparison_forward
#print axioms Atlas.Lattices.icosianComparison_reverse
#print axioms Atlas.Lattices.icosianComparison_lattice_iff
#print axioms Atlas.Lattices.icosianComparison_lattice_surjective
#print axioms Atlas.Lattices.icosianLeechEquiv
#print axioms Atlas.Lattices.icosianLeechEquiv_isometry
#print axioms Atlas.Lattices.icosianLeech_rank
#print axioms Atlas.Lattices.icosianHermitian_of_bilinear_and_right_linear
#print axioms Atlas.Lattices.icosian_right_linear_of_generators
#print axioms Atlas.Lattices.icosianScalarRepresentation
#print axioms Atlas.Lattices.icosianScalarRepresentation_bilinear
#print axioms Atlas.Lattices.icosianScalarRepresentation_lattice_iff
#print axioms Atlas.Lattices.icosian_right_linear_iff_scalar_commutation
#print axioms Atlas.Conway.icosianScalarsToCo0
#print axioms Atlas.Conway.icosianScalarsToCo0_injective
#print axioms Atlas.Conway.icosianScalarsToCo0_range_card
#print axioms Atlas.Conway.icosianHermitianGroup_iff
#print axioms Atlas.Conway.icosianHermitianToCo0_injective
#print axioms Atlas.Conway.icosianHermitianToCo0_range
#print axioms Atlas.Conway.icosianCentralizerEquiv
#print axioms Atlas.Lattices.icosianHermitian_integral
#print axioms Atlas.Lattices.icosianReflection_lattice
#print axioms Atlas.Lattices.icosianReflection_involutive
#print axioms Atlas.Lattices.icosianReflection_hermitian
#print axioms Atlas.Codes.icosianMatrixGlue_adjugate_pairing
#print axioms Atlas.Conway.icosianHermitianGroup_finite
#print axioms Atlas.Conway.icosianReflectionEquiv_mem
#print axioms Atlas.Conway.icosianRootReflection
#print axioms Atlas.Conway.icosianRootReflection_square
#print axioms Atlas.Algebra.icosianNorm_discriminant_nonneg
#print axioms Atlas.Algebra.icosianIntegralNorm_discriminant_nonneg
#print axioms Atlas.Algebra.icosianIntegralNorm_real_zero
#print axioms Atlas.Algebra.icosianIntegralNorm_im_of_real_one
#print axioms Atlas.Algebra.icosianIntegralNorm_im_of_real_two
#print axioms Atlas.Algebra.icosianNorm_triple_arithmetic
#print axioms Atlas.Lattices.icosianLeechModule_zero_even_norms
#print axioms Atlas.Lattices.icosianRoot_integral_norm_sum
#print axioms Atlas.Lattices.icosianRoot_norm_shapes
#print axioms Atlas.Lattices.icosianAxisRoot_surjective
#print axioms Atlas.Lattices.icosianAxisRootEquiv
#print axioms Atlas.Lattices.icosianAxisRoots_card
#print axioms Atlas.Codes.icosianDetRowEquiv
#print axioms Atlas.Codes.icosianDeterminantGlueEquiv
#print axioms Atlas.Codes.icosianDeterminantGlue_card
#print axioms Atlas.Codes.icosianDeterminantGlue_card_four
#print axioms Atlas.Algebra.icosianNormTwo_right_associate
#print axioms Atlas.Algebra.icosianNormTwo_associate_of_adjugate
#print axioms Atlas.Algebra.icosianNormTwoRepresentative_norm
#print axioms Atlas.Algebra.icosianNormTwoRepresentative_cover
#print axioms Atlas.Algebra.icosianNormTwoRepresentative_separate
#print axioms Atlas.Algebra.icosianNormTwoEquiv
#print axioms Atlas.Algebra.icosianNormTwo_card
#print axioms Atlas.Algebra.icosianNormTwo_reduction_ne_zero
#print axioms Atlas.Algebra.icosianNormOneReduction_fiber_card
#print axioms Atlas.Algebra.icosianNormTwoMatrixParameters_count
#print axioms Atlas.Algebra.icosianNormTwoReductionFiberEquiv
#print axioms Atlas.Algebra.icosianNormTwoReduction_fiber_card
#print axioms Atlas.Algebra.icosianNormTwoReduction_surjective_rank_one
#print axioms Atlas.Lattices.icosianRootPermute
#print axioms Atlas.Lattices.icosianEdgePairs_card
#print axioms Atlas.Lattices.icosianEdgeRootEquiv
#print axioms Atlas.Lattices.icosianEdgeRoots_card
#print axioms Atlas.Lattices.icosianEdgeRoot_recognition
#print axioms Atlas.Algebra.icosianUnitNormEquiv
#print axioms Atlas.Algebra.icosianGoldenToOrder_reduction
#print axioms Atlas.Algebra.icosianUnitNormFiber_card
#print axioms Atlas.Algebra.icosianGoldenUnitNormFiber_card
#print axioms Atlas.Lattices.icosianRootsWithNormsEquiv
#print axioms Atlas.Lattices.icosianRootsWithNorms_card
#print axioms Atlas.Lattices.icosianRootCStandard_card
#print axioms Atlas.Lattices.icosianRootDStandard_card
#print axioms Atlas.Lattices.icosianRoot_scalar_norm
#print axioms Atlas.Lattices.icosianRoot_scalar_integral
#print axioms Atlas.Lattices.icosianRoot_scalar_unit
#print axioms Atlas.Conway.icosianRootPoint_eq_iff
#print axioms Atlas.Conway.icosianRootLineFiber_card
#print axioms Atlas.Conway.icosianRootPoint_card_of_root_card
#print axioms Atlas.Conway.icosianMonomialReduction_surjective
#print axioms Atlas.Conway.icosianLiftedMonomialProjection_surjective
#print axioms Atlas.Conway.icosianLiftedMonomialProjection_kernel_card
#print axioms Atlas.Conway.icosianLiftedMonomial_card
#print axioms Atlas.Conway.icosianMonomialToHermitian_injective
#print axioms Atlas.Lattices.icosianAxisIntersection
#print axioms Atlas.Conway.icosianFrameMonomial_mem
#print axioms Atlas.Conway.icosianMonomial_range_eq_frameStabilizer
#print axioms Atlas.Conway.icosianCoordinateFrameStabilizer_card
#print axioms Atlas.triple_perm_exists
#print axioms Atlas.Lattices.icosianRootCFamily_card
#print axioms Atlas.Lattices.icosianRootDFamily_card
#print axioms Atlas.Lattices.icosianRootShape_unique
#print axioms Atlas.Lattices.icosianRootShape_exhaustive
#print axioms Atlas.Lattices.icosianRootShapeEquiv
#print axioms Atlas.Lattices.icosianRoots_card
#print axioms Atlas.Conway.icosianRootPoint_card
#print axioms Atlas.Conway.icosianHermitian_root_mulAction
#print axioms Atlas.Conway.icosianHermitian_rootPoint_mulAction
#print axioms Atlas.Conway.icosianRootPointOrthogonal_iff
#print axioms Atlas.Conway.icosianRootPointOrthogonal_smul_iff
#print axioms Atlas.Lattices.icosianZeroRoots_card
#print axioms Atlas.Conway.icosianAxisNeighbors_card
#print axioms Atlas.Algebra.icosianNormTwoPair_orthogonal
#print axioms Atlas.Conway.icosianEdgeRootBase_complement_unique
#print axioms Atlas.Conway.icosianRootAxis_completion
#print axioms Atlas.Combinatorics.triangleEdgeEquiv
#print axioms Atlas.Combinatorics.regular_unique_triangle_count
#print axioms Atlas.Combinatorics.regular_unique_triangle_count_315_10
#print axioms Atlas.Conway.icosianRootFrame_card_of_local_geometry
#print axioms Atlas.Conway.icosianEightNeighborScalar_norm
#print axioms Atlas.Conway.icosianEightNeighborScalar_reduction
#print axioms Atlas.Conway.icosianEightNeighborPoint_injective
#print axioms Atlas.Conway.icosianAxisNeighborCatalogue_bijective
#print axioms Atlas.Conway.icosianEightNeighborPoint_orthogonal_partner
#print axioms Atlas.Conway.icosianFiveAxisFrames_exhaust
#print axioms Atlas.Conway.icosianHermitian_rootFrame_mulAction
#print axioms Atlas.Conway.icosianRootNeighbors_card_of_normalizer
#print axioms Atlas.Conway.icosianRoot_completion_of_normalizer
#print axioms Atlas.Conway.icosianRootFrame_card_of_normalizers
#print axioms Atlas.Conway.icosianLocalCoordinateRootFrame_stabilizer
#print axioms Atlas.Conway.icosianLocalCoordinateRootFrame_stabilizer_card
#print axioms Atlas.Conway.icosianAxisRootFrames_card
#print axioms Atlas.Conway.icosianLocalDReductionTest_iff
#print axioms Atlas.Conway.icosianRootPoint_local_orbit
#print axioms Atlas.Conway.icosianRootPoint_local_orbit_card
#print axioms Atlas.Conway.icosianRootPoint_local_stabilizer_card
#print axioms Atlas.Conway.icosianRootPoint_local_orbits_exhaustive
#print axioms Atlas.Conway.icosianRootPoint_local_orbits_disjoint
#print axioms Atlas.Conway.icosianRootPointShape_card
#print axioms Atlas.Conway.icosianRootPointShape_unique
#print axioms Atlas.Conway.icosianRootPointShape_exhaustive
#print axioms Atlas.Conway.icosianCoordinateFrame_rootPoint_shape
#print axioms Atlas.Conway.icosianMonomial_line_iff
#print axioms Atlas.Conway.icosianMonomial_line_determined
#print axioms Atlas.Conway.icosianLocalCScalarCandidates_card
#print axioms Atlas.Conway.icosianLocalCLine_scalar_test
#print axioms Atlas.Conway.icosianLocalCStabilizer_card_le
#print axioms Atlas.Conway.icosianLocalC_full_frame_orbit
#print axioms Atlas.Conway.icosianLocalC_full_frame_stabilizer_card
#print axioms Atlas.Conway.icosianLocalDReductionParameters_card
#print axioms Atlas.Conway.icosianLocalDUnitParameters_card
#print axioms Atlas.Conway.icosianLocalDLine_reduction_test
#print axioms Atlas.Conway.icosianLocalDStabilizer_card_le
#print axioms Atlas.Conway.icosianLocalD_full_frame_orbit
#print axioms Atlas.Conway.icosianLocalD_full_frame_stabilizer_card
#print axioms Atlas.Conway.icosianUpperSL2_card
#print axioms Atlas.Conway.icosianUpperUnit_card
#print axioms Atlas.Conway.icosianRepeatedUnitParameters_card
#print axioms Atlas.Conway.icosianLocalBStabilizer_card_le
#print axioms Atlas.Conway.icosianLocalB_full_frame_orbit
#print axioms Atlas.Conway.icosianLocalB_full_frame_stabilizer_card
#print axioms Atlas.Conway.icosianLocalA_full_frame_orbit
#print axioms Atlas.Conway.icosianLocalA_full_frame_stabilizer_card
#print axioms Atlas.Conway.icosianRootPoint_normalizers
#print axioms Atlas.Conway.icosianRootNeighbors_card
#print axioms Atlas.Conway.icosianRootPoint_completion
#print axioms Atlas.Conway.icosianRootFrames_card

#print axioms Atlas.Conway.icosianReflectionDiagonalIntegral_mem

#print axioms Atlas.Conway.icosianReflectionDiagonalRoot_norm

#print axioms Atlas.Conway.icosianReflectionDiagonalWord_linear

#print axioms Atlas.Conway.icosianReflectionDiagonalMonomial_reduction

#print axioms Atlas.Conway.icosianReflectionEdgeIntegral_mem

#print axioms Atlas.Conway.icosianReflectionEdgeRoot_norm

#print axioms Atlas.Conway.icosianReflectionEdgeWord_linear

#print axioms Atlas.Conway.icosianReflectionEdgeMonomial_reduction

#print axioms Atlas.Conway.icosianReflectionDiagonalWord_mem_reflections

#print axioms Atlas.Conway.icosianReflectionEdgeWord_mem_reflections

#print axioms Atlas.Conway.icosianReflectionSwap_linear

#print axioms Atlas.Conway.icosian_full_glue_generated_by_reflections

#print axioms Atlas.Conway.icosian_full_frame_generated_by_reflections

#print axioms Atlas.Conway.icosianMonomial_kernel_mem_reflections

#print axioms Atlas.Conway.icosianLineReflection_conjugate

#print axioms Atlas.Conway.icosian_fix_rootPoints_commutes_reflections

#print axioms Atlas.Conway.icosian_fix_rootPoints_eq_sign

#print axioms Atlas.Conway.icosian_full_monomial_centralizer_iff

#print axioms Atlas.Conway.icosianHermitian_center

#print axioms Atlas.Conway.icosianCentralSigns_card

#print axioms Atlas.Conway.icosian_rootPoint_kernel

#print axioms Atlas.Conway.icosianProjectivePointHom_injective

#print axioms Atlas.Conway.icosianProjectivePoint_faithful

#print axioms Atlas.Conway.icosianProjective_card_mul_two

#print axioms Atlas.GroupTheory.frame_involution_commutator

#print axioms Atlas.GroupTheory.perfect_of_transitive_commutator_family

#print axioms Atlas.Conway.icosianAxisTransitionRoot_norm

#print axioms Atlas.Conway.icosianAxisTransitionIntegral_mem

#print axioms Atlas.Conway.icosianAxisTransitionWord_mem

#print axioms Atlas.Conway.icosianAxisTransitionRaw_axes

#print axioms Atlas.Conway.icosianRootToPoint_smul_eq_of_rightMul

#print axioms Atlas.Conway.icosianAxisTransitionWord_axis

#print axioms Atlas.Conway.icosianAxisTransitionWord_fixes_axis

#print axioms Atlas.Conway.icosianAxisTransitionWord_frame

#print axioms Atlas.Conway.icosianReflectionGroup_transitive_axis_frames

#print axioms Atlas.Conway.icosianReflectionGroup_frame_normalizer

#print axioms Atlas.Conway.icosianReflectionGroup_frame_pretransitive

#print axioms Atlas.Conway.icosianHermitian_frame_pretransitive

#print axioms Atlas.Conway.icosianReflectionGroup_eq_top

#print axioms Atlas.Conway.icosianHermitian_order

#print axioms Atlas.Conway.icosianCentralizer_order

#print axioms Atlas.Conway.icosianProjective_order

#print axioms Atlas.Conway.icosianProjective_order_factorization

#print axioms Atlas.Conway.icosianHermitian_frame_order_identity

#print axioms Atlas.Conway.icosianRootPointShapeNormLevel_card_mul

#print axioms Atlas.Conway.icosianRootPointShapeNormLevel_nine_card

#print axioms Atlas.Conway.icosianNineLocalData_injective

#print axioms Atlas.Conway.icosianRootPointShapeNormLevel_nine_exhaustive

#print axioms Atlas.Conway.icosianAxisLinkBImage_shape

#print axioms Atlas.Conway.icosianAxisLinkCImage_shape

#print axioms Atlas.Conway.icosianAxisOrbit_A_B

#print axioms Atlas.Conway.icosianAxisOrbit_B_C

#print axioms Atlas.Conway.icosianAxisOrbit_C_D

#print axioms Atlas.Conway.icosianNineNormFusion_cases

#print axioms Atlas.Conway.icosianSameAxisOrbit_of_norm

#print axioms Atlas.Conway.icosianFullAxisStabilizer_orbit

#print axioms Atlas.Conway.icosianFullAxisStabilizer_orbit_card

#print axioms Atlas.stabilizer_transitive_of_reference_invariant

#print axioms Atlas.Conway.icosianEqualCoordinate_swap_fixes

#print axioms Atlas.Conway.icosianRootLocalVector_equal_norm

#print axioms Atlas.Conway.icosianMonomialPoint_norm_invariant

#print axioms Atlas.Conway.icosianReference_axis_transitive

#print axioms Atlas.Conway.icosianCoordinateAxis_shape_norm_transitive

#print axioms Atlas.Conway.icosianAxisStabilizer_root_norm

#print axioms Atlas.Conway.icosianAxisStabilizer_point_norm

#print axioms Atlas.Conway.icosianProjective_simple

#print axioms Atlas.Conway.icosianProjective_nonabelian

#print axioms Atlas.Conway.icosianProjective_perfect

#print axioms Atlas.Conway.icosianProjective_rootPoint_primitive

#print axioms Atlas.Conway.icosianHermitian_rootPoint_primitive

#print axioms Atlas.Conway.icosianProjective_frame_commutator

#print axioms Atlas.Conway.icosianProjectiveReflection_generation

#print axioms Atlas.Conway.icosianProjectiveLineInvolutions_normal

#print axioms Atlas.Conway.icosianProjectiveLineInvolutions_normalClosure

#print axioms Atlas.Conway.icosianProjectiveLineInvolutions_abelian

#print axioms Atlas.Conway.icosianProjectiveLineInvolutions_le_stabilizer

#print axioms Atlas.Conway.icosianProjectiveAxisReflection_ne_one

#print axioms Atlas.Conway.icosian_six_suborbit_block_arithmetic

#print axioms Atlas.Conway.icosianRootSuborbitLabel_fiber_card

#print axioms Atlas.Conway.icosianProjectiveReflection_square

#print axioms Atlas.Conway.icosianProjectiveReflection_fixes

#print axioms Atlas.Conway.icosianRightLinear_apply_two_axes

#print axioms Atlas.Conway.icosianAxisTransitionWord_matrix_apply

#print axioms Atlas.Conway.icosianAxisTransition_B_C_norm

#print axioms Atlas.Conway.icosianAxisTransition_C_D_norm

#print axioms Atlas.Sporadic.Janko2.finite

#print axioms Atlas.Sporadic.Janko2.card

#print axioms Atlas.Sporadic.Janko2.order

#print axioms Atlas.Sporadic.Janko2.linear_card

#print axioms Atlas.Sporadic.Janko2.isSimpleGroup

#print axioms Atlas.Sporadic.Janko2.nonabelian

#print axioms Atlas.Sporadic.Janko2.perfect

#print axioms Atlas.Sporadic.Janko2.exists_mul_ne_mul

#print axioms Atlas.Sporadic.Janko2.center

#print axioms Atlas.Sporadic.Janko2.center_card

#print axioms Atlas.Sporadic.Janko2.right_scalar_card

#print axioms Atlas.Sporadic.Janko2.embedding_injective

#print axioms Atlas.Sporadic.Janko2.projection_surjective

#print axioms Atlas.Sporadic.Janko2.toConway1_injective

#print axioms Atlas.Sporadic.Janko2.toConway1_compatible

#print axioms Atlas.Sporadic.Janko2.scalar_intersection

#print axioms Atlas.Sporadic.Janko2.scalar_commutation

#print axioms Atlas.Sporadic.Janko2.central_product_kernel

#print axioms Atlas.Sporadic.Janko2.central_product_injective

#print axioms Atlas.Sporadic.Janko2.alternatingProductToConway1_injective

#print axioms Atlas.Sporadic.Janko2.integralRightScalars_injective

#print axioms Atlas.Sporadic.Janko2.integralRightScalars_comparison

#print axioms Atlas.Sporadic.Janko2.integralRightScalars_unit

#print axioms Atlas.Sporadic.Janko2.glue_comparison_reduction

#print axioms Atlas.Sporadic.Janko2.glue_quotient_card

#print axioms Atlas.Sporadic.Janko2.lattice_axes_sum

#print axioms Atlas.Sporadic.Janko2.lattice_comparison_onto

#print axioms Atlas.Sporadic.Janko2.lattice_comparison_isometry

#print axioms Atlas.Sporadic.Janko2.integral_rank

#print axioms Atlas.Sporadic.Janko2.integral_free

#print axioms Atlas.Sporadic.Janko2.integral_finite

#print axioms Atlas.Sporadic.Janko2.right_scalar_closed

#print axioms Atlas.Sporadic.Janko2.quaternionic_rank

#print axioms Atlas.Sporadic.Janko2.golden_rank

#print axioms Atlas.Sporadic.Janko2.rational_rank

#print axioms Atlas.Sporadic.Janko2.full_centralizer

#print axioms Atlas.Sporadic.Janko2.linear_faithful

#print axioms Atlas.Sporadic.Janko2.linear_right_linear

#print axioms Atlas.Sporadic.Janko2.linear_hermitian

#print axioms Atlas.Sporadic.Janko2.linear_lattice

#print axioms Atlas.Sporadic.Janko2.degree

#print axioms Atlas.Sporadic.Janko2.faithful

#print axioms Atlas.Sporadic.Janko2.primitive

#print axioms Atlas.Sporadic.Janko2.transitive

#print axioms Atlas.Sporadic.Janko2.quaternionic_projective_faithful

#print axioms Atlas.Sporadic.Janko2.quaternionic_projective_kernel

#print axioms Atlas.Sporadic.Janko2.point_kernel

#print axioms Atlas.Sporadic.Janko2.frame_count

#print axioms Atlas.Sporadic.Janko2.frame_size

#print axioms Atlas.Sporadic.Janko2.frame_orthogonal

#print axioms Atlas.Sporadic.Janko2.frame_transitive

#print axioms Atlas.Sporadic.Janko2.full_frame_stabilizer

#print axioms Atlas.Sporadic.Janko2.frame_stabilizer_card

#print axioms Atlas.Sporadic.Janko2.orthogonal_count

#print axioms Atlas.Sporadic.Janko2.orthogonal_completion

#print axioms Atlas.Sporadic.Janko2.reflection_square

#print axioms Atlas.Sporadic.Janko2.reflection_order

#print axioms Atlas.Sporadic.Janko2.local_reflection_card

#print axioms Atlas.Sporadic.Janko2.local_reflection_central

#print axioms Atlas.Sporadic.Janko2.reflection_conjugate

#print axioms Atlas.Sporadic.Janko2.reflection_generation

#print axioms Atlas.Sporadic.Janko2.full_reflection_generation

#print axioms Atlas.Sporadic.Janko2.angle_invariant

#print axioms Atlas.Sporadic.Janko2.angle_values_injective

#print axioms Atlas.Sporadic.Janko2.angle_exhaustive

#print axioms Atlas.Sporadic.Janko2.angle_card

#print axioms Atlas.Sporadic.Janko2.angle_stabilizer_orbit

#print axioms Atlas.Sporadic.Janko2.suborbit_card

#print axioms Atlas.Sporadic.Janko2.suborbit_cover

#print axioms Atlas.Sporadic.Janko2.suborbit_pairwise

#print axioms Atlas.Sporadic.Janko2.suborbit_is_orbit

#print axioms Atlas.Sporadic.Janko2.construction

#print axioms Atlas.Sporadic.Janko2.construction_complete

#print axioms Atlas.Sporadic.Janko2.exists_model

#print axioms Atlas.Conway.icosianProjectiveReflection_ne_one

#print axioms Atlas.Conway.icosianProjectiveReflection_order

#print axioms Atlas.Conway.icosianProjectiveLineInvolutions_card

#print axioms Atlas.Conway.icosianProjectiveLineInvolutions_central

#print axioms Atlas.Conway.icosianHermitianToCo0_sign

#print axioms Atlas.Conway.icosianCentralSigns_eq_comap

#print axioms Atlas.Conway.icosianProjectiveToCo1_injective

#print axioms Atlas.Conway.icosianProjectiveToCo1_mk

#print axioms Atlas.Conway.icosianScalarsToCo0_minusOne

#print axioms Atlas.Conway.icosianHermitian_eq_sign_of_scalar

#print axioms Atlas.Conway.icosianScalars_inf_centralizer

#print axioms Atlas.Conway.icosianScalars_commute_Hermitian

#print axioms Atlas.Conway.icosianScalarCentralProduct_kernel_iff

#print axioms Atlas.Conway.icosianCentralProductToCo0_injective

#print axioms Atlas.Algebra.icosianNormOneReduction_kernel_iff

#print axioms Atlas.Algebra.icosianScalarProjectiveSL

#print axioms Atlas.Algebra.icosianScalarProjective_card

#print axioms Atlas.Algebra.goldenFour_SL_center

#print axioms Atlas.Algebra.goldenFourSLPSL

#print axioms Atlas.Algebra.goldenFourProjectiveLine_card

#print axioms Atlas.Algebra.goldenFourPSLToFivePerm_injective

#print axioms Atlas.Algebra.goldenFourPSLToFivePerm_sign

#print axioms Atlas.Algebra.goldenFourPSLToAlternating_bijective

#print axioms Atlas.Algebra.goldenFourSLAlternatingFive

#print axioms Atlas.Conway.icosianScalarSigns_eq_comap

#print axioms Atlas.Conway.icosianScalarProjectiveToCo1_injective

#print axioms Atlas.Conway.icosianScalarProjective_ranges_disjoint

#print axioms Atlas.Conway.icosianScalarProjectiveProductToCo1_injective

#print axioms Atlas.Conway.icosianScalarProjectiveAlternating

#print axioms Atlas.Conway.icosianAlternatingProjectiveToCo1_injective

#print axioms Atlas.Lattices.icosianIntegralRightScalars_apply

#print axioms Atlas.Lattices.icosianLeechRightScalars_comparison

#print axioms Atlas.Lattices.icosianLeechRightScalars_rational

#print axioms Atlas.Lattices.icosianIntegralRightScalars_injective

#print axioms Atlas.Lattices.icosianLeechRightScalars_injective

#print axioms Atlas.Conway.icosianLeechRightScalars_unit

#print axioms Atlas.Lattices.icosianLatticeGlueReduction_surjective

#print axioms Atlas.Lattices.icosianLatticeTwice_mem

#print axioms Atlas.Lattices.icosianLatticeGlueQuotient

#print axioms Atlas.Lattices.icosianLatticeGlueQuotient_mk

#print axioms Atlas.Lattices.icosianLatticeGlueQuotient_card

#print axioms Atlas.Lattices.icosianTwiceCoordinates_mem

#print axioms Atlas.Lattices.icosianAxisDirectSumEquiv

#print axioms Atlas.Lattices.icosianLatticeAxes_iSup

#print axioms Atlas.Lattices.icosianLatticeTwice_eq_axes_comap

#print axioms Atlas.Lattices.icosianAxisExternalDirectSumEquiv

#print axioms Atlas.Conway.icosianRootAngle_normalized

#print axioms Atlas.Conway.icosianRootAngle_right_units

#print axioms Atlas.Conway.icosianRootPointAngle_toPoint

#print axioms Atlas.Conway.icosianRootPointAngle_smul

#print axioms Atlas.Conway.icosianRootPointAngle_symm

#print axioms Atlas.Conway.icosianRootPointAngle_self

#print axioms Atlas.Conway.icosianRootPointAngle_zero_iff

#print axioms Atlas.Conway.icosianRootPointAngle_axis

#print axioms Atlas.Conway.icosianRootPointAngleValues_injective

#print axioms Atlas.Conway.icosianRootPointAngleLevel_card

#print axioms Atlas.Conway.icosianRootPointAngle_exhaustive

#print axioms Atlas.Conway.icosianRootPointAngle_projective_smul

#print axioms Atlas.Fischer.theta_sq

#print axioms Atlas.Fischer.theta_conjugate

#print axioms Atlas.Fischer.theta_integral

#print axioms Atlas.Fischer.cube_eq_one_iff

#print axioms Atlas.Fischer.mu3_card

#print axioms Atlas.Fischer.scalarToComplex_injective

#print axioms Atlas.Fischer.scalarToComplex_star

#print axioms Atlas.Fischer.scalarToComplex_real

#print axioms Atlas.Fischer.scalarToComplex_normSq

#print axioms Atlas.Fischer.scalar_norm_positive

#print axioms Atlas.Fischer.weightedHermitian_smul_left

#print axioms Atlas.Fischer.weightedHermitian_smul_right

#print axioms Atlas.Fischer.weightedHermitian_star

#print axioms Atlas.Fischer.weightedHermitian_positive

#print axioms Atlas.Fischer.coordinates_dimension

#print axioms Atlas.Fischer.axisCoordinates_dimension

#print axioms Atlas.Fischer.octadCoordinates_dimension

#print axioms Atlas.Fischer.hermitian_positive

#print axioms Atlas.Fischer.hermitian_nondegenerate

#print axioms Atlas.Fischer.hermitian_u

#print axioms Atlas.Fischer.hermitian_xOctad

#print axioms Atlas.Fischer.hermitian_u_xOctad

#print axioms Atlas.Fischer.basicAxis_norm

#print axioms Atlas.Fischer.signedOctadEquiv

#print axioms Atlas.Fischer.signedOctadVector_negate

#print axioms Atlas.Fischer.signedOctadVector_canonical

#print axioms Atlas.Fischer.signedOctadVector_norm

#print axioms Atlas.Fischer.signedOctadAssignment_ext

#print axioms Atlas.GroupTheory.normal_sup_generator_eq_top

#print axioms Atlas.GroupTheory.commutator_le_normal_of_primitive_generators

#print axioms Atlas.GroupTheory.simple_of_perfect_primitive_generators

#print axioms Atlas.GroupTheory.factorSwapFixedEquiv

#print axioms Atlas.GroupTheory.card_fixed_factorSwap

#print axioms Atlas.GroupTheory.card_eq_sq_fixed_factorSwap

#print axioms Atlas.GroupTheory.subgroup_map_involution

#print axioms Atlas.GroupTheory.involutive_normal_factors

#print axioms Atlas.GroupTheory.exists_equiv_factorSwap

#print axioms Atlas.GroupTheory.card_eq_sq_fixed_of_normal_factors

#print axioms Atlas.GroupTheory.exists_mulEquiv_factorSwap

#print axioms Atlas.GroupTheory.index_two_involution_normal_form

#print axioms Atlas.GroupTheory.normal_map_of_index_two_invariant

#print axioms Atlas.GroupTheory.index_two_invariant_normal_dichotomy

#print axioms Atlas.GroupTheory.index_two_transitive_of_outside_fixed

#print axioms Atlas.GroupTheory.conjNormal_fixed_iff_stabilizer

#print axioms Atlas.GroupTheory.simple_derived_of_primitive_involutions

#print axioms Atlas.GroupTheory.simple_derived_of_primitive_involution_class

#print axioms Atlas.Fischer.cocodeFunctional_apply

#print axioms Atlas.Fischer.cocodeFunctional_ker

#print axioms Atlas.Fischer.binaryDot_surjective

#print axioms Atlas.Fischer.cocodeFunctional_surjective

#print axioms Atlas.Fischer.cocodeDualEquiv_mk

#print axioms Atlas.Fischer.cocodeParity_mk

#print axioms Atlas.Fischer.cocode_finrank

#print axioms Atlas.Fischer.cocode_card

#print axioms Atlas.Fischer.parkerFactorSet_zero_left

#print axioms Atlas.Fischer.parkerFactorSet_zero_right

#print axioms Atlas.Fischer.parkerFactorSet_defect

#print axioms Atlas.Fischer.parkerMultiply_one_left

#print axioms Atlas.Fischer.parkerMultiply_one_right

#print axioms Atlas.Fischer.parkerMultiply_square

#print axioms Atlas.Fischer.parkerMultiply_leftDivide

#print axioms Atlas.Fischer.parkerLeftDivide_multiply

#print axioms Atlas.Fischer.parkerMultiply_rightDivide

#print axioms Atlas.Fischer.parkerRightDivide_multiply

#print axioms Atlas.Fischer.parkerOrderedTheta_add_left

#print axioms Atlas.Fischer.parkerOrderedTheta_add_middle

#print axioms Atlas.Fischer.parkerOrderedTheta_add_right

#print axioms Atlas.Fischer.parkerOrderedBeta_add_left

#print axioms Atlas.Fischer.parkerOrderedBeta_add_right

#print axioms Atlas.Fischer.parkerOrderedFactorSet_defect

#print axioms Atlas.Fischer.parkerOrderedTheta_polarize

#print axioms Atlas.Fischer.parkerGolayFactorSet_zero_left

#print axioms Atlas.Fischer.parkerGolayFactorSet_zero_right

#print axioms Atlas.Fischer.parkerLoopMultiply_one_left

#print axioms Atlas.Fischer.parkerLoopMultiply_one_right

#print axioms Atlas.Fischer.parkerGolayFactorSet_defect

#print axioms Atlas.Fischer.parkerTripleIntersection_swap

#print axioms Atlas.Fischer.parkerTripleIntersection_repeat

#print axioms Atlas.Fischer.parkerGolay_coordinate_expand

#print axioms Atlas.Fischer.parkerTripleIntersection_basis_expand

#print axioms Atlas.Fischer.parkerGolayFactorSet_associator

#print axioms Atlas.Fischer.parkerGolayFactorSet_square

#print axioms Atlas.Fischer.parkerGolayFactorSet_commutator

#print axioms Atlas.Fischer.parkerLoopMultiply_square

#print axioms Atlas.Fischer.parkerLoopMultiply_commutator

#print axioms Atlas.Fischer.parkerLoopMultiply_associator

#print axioms Atlas.Fischer.parkerOmega_square

#print axioms Atlas.Fischer.parkerOmega_commutes

#print axioms Atlas.Fischer.parkerOmega_associates_left

#print axioms Atlas.Fischer.parkerOmega_associates_middle

#print axioms Atlas.Fischer.parkerOmega_associates_right

#print axioms Atlas.Fischer.parkerLoopLift_preserves_multiply

#print axioms Atlas.Fischer.parkerLoopLift_sign

#print axioms Atlas.Fischer.parkerLoopLift_fixes_sign

#print axioms Atlas.Fischer.parkerCodeEquiv_faithful

#print axioms Atlas.Fischer.parkerCodeEquiv_weight

#print axioms Atlas.Fischer.parkerCodeEquiv_triple

#print axioms Atlas.Fischer.golayQuarterWeight_add

#print axioms Atlas.Fischer.golayHalfOverlap_add_left

#print axioms Atlas.Fischer.product_add_left

#print axioms Atlas.Fischer.product_add_right

#print axioms Atlas.Fischer.product_smul_left

#print axioms Atlas.Fischer.product_smul_right

#print axioms Atlas.Fischer.product_coordinateVector

#print axioms Atlas.Fischer.product_u

#print axioms Atlas.Fischer.product_u_xOctad

#print axioms Atlas.Fischer.product_xOctad_u

#print axioms Atlas.Fischer.product_xOctad

#print axioms Atlas.Fischer.product_scaledAxis_self

#print axioms Atlas.Fischer.product_scaledAxis_distinct

#print axioms Atlas.Fischer.product_scaledAxis_octad

#print axioms Atlas.Fischer.product_octad_self

#print axioms Atlas.Fischer.product_octad_four

#print axioms Atlas.Fischer.product_octad_disjoint

#print axioms Atlas.Fischer.product_octad_two

#print axioms Atlas.Fischer.octadReplication_five

#print axioms Atlas.Fischer.octadReplication_four

#print axioms Atlas.Fischer.octadReplication_three

#print axioms Atlas.Fischer.octadReplication_two

#print axioms Atlas.Fischer.octadReplication_one

#print axioms Atlas.Fischer.octadReplication_zero

#print axioms Atlas.Fischer.octadReplication_formula

#print axioms Atlas.Fischer.octad_intersection_moment

#print axioms Atlas.Algebra.binary_cocycle_exists_correction

#print axioms Atlas.Algebra.binary_corrections_differ_by_linear

#print axioms Atlas.Algebra.binary_correction_add_linear

#print axioms Atlas.Combinatorics.block_extension_count

#print axioms Atlas.Combinatorics.subblock_incidence_sum

#print axioms Atlas.Combinatorics.subblock_incidence_count

#print axioms Atlas.Fischer.signedOctadPresentation

#print axioms Atlas.Fischer.octad_product_four_weight

#print axioms Atlas.Fischer.octad_product_disjoint_weight

#print axioms Atlas.Fischer.product_comm

#print axioms Atlas.Fischer.rootMap_phase

#print axioms Atlas.Fischer.root_phase

#print axioms Atlas.Fischer.octad_triangle_sign

#print axioms Atlas.Fischer.octad_complementary_trio_sign

#print axioms Atlas.Fischer.octadBasisProduct_octad_apply

#print axioms Atlas.Fischer.cubic_basis_swap_first

#print axioms Atlas.Fischer.cubic_swap_first

#print axioms Atlas.Fischer.cubic_swap_last

#print axioms Atlas.Fischer.basicAxis_isRoot

#print axioms Atlas.Fischer.basicAxis_product

#print axioms Atlas.Fischer.nonorthogonal_root_rigidity

#print axioms Atlas.Fischer.rootMap_covariance_linear

#print axioms Atlas.Fischer.rootMap_covariance_conjugate

#print axioms Atlas.Fischer.rootMap_basicAxis_u

#print axioms Atlas.Fischer.rootMap_basicAxis_xOctad

#print axioms Atlas.Fischer.root_scalar_iff

#print axioms Atlas.Fischer.negative_not_root

#print axioms Atlas.Fischer.scalarPhaseEquiv_product

#print axioms Atlas.Fischer.scalarPhaseEquiv_hermitian

#print axioms Atlas.Fischer.rootMap_basicAxis_eq_cocode

#print axioms Atlas.Fischer.basicAxis_rootMap_antiunitary

#print axioms Atlas.Fischer.cocodeInvolution_order

#print axioms Atlas.Fischer.cocodeInvolutions_relation

#print axioms Atlas.Fischer.cocodeInvolutions_generate

#print axioms Atlas.Fischer.cocodeCoordinateRepresentation_injective

#print axioms Atlas.Fischer.cocodeCoordinateRepresentation_generator

#print axioms Atlas.Fischer.cocodeReflection_relations

#print axioms Atlas.Fischer.basicAxis_rootMap_involutive

#print axioms Atlas.Fischer.basicAxis_rootMap_order

#print axioms Atlas.Fischer.cocodeReflectionGroup_order

#print axioms Atlas.Fischer.cocodeReflections_generate

#print axioms Atlas.Fischer.basicAxis_rootMap_product

#print axioms Atlas.Fischer.basicAxis_isReflectingRoot

#print axioms Atlas.Fischer.parkerMathieu_exists_correction

#print axioms Atlas.Fischer.parkerMathieuLift_multiply

#print axioms Atlas.Fischer.parkerMathieuLift_sign

#print axioms Atlas.Fischer.parkerStandardProjection_surjective

#print axioms Atlas.Fischer.parkerCocodeKernelEquiv

#print axioms Atlas.Fischer.parkerCocodeEmbedding_injective

#print axioms Atlas.Fischer.parkerCocodeEmbedding_range

#print axioms Atlas.Fischer.parkerStandardGroup_order

#print axioms Atlas.Fischer.parkerStandardGroup_order_value

#print axioms Atlas.Fischer.parkerStandardParity_cocode

#print axioms Atlas.Fischer.parkerStandardParity_surjective

#print axioms Atlas.Fischer.parkerStandardPlusProjection_surjective

#print axioms Atlas.Fischer.parkerStandardPlus_index

#print axioms Atlas.Fischer.parkerStandardPlus_order

#print axioms Atlas.Fischer.parkerStandardPlus_order_value

#print axioms Atlas.Fischer.parkerCentral_iff

#print axioms Atlas.Fischer.parkerCentral_four_forms

#print axioms Atlas.Fischer.parkerCenter_card

#print axioms Atlas.Fischer.parkerTripleIntersection_radical

#print axioms Atlas.Fischer.parkerCoordinateAction_hermitian

#print axioms Atlas.Fischer.parkerCoordinateAction_basis

#print axioms Atlas.Fischer.parkerCoordinateAction_u

#print axioms Atlas.Fischer.parkerCoordinateAction_xOctad

#print axioms Atlas.Fischer.parkerCoordinateAction_signedOctad

#print axioms Atlas.Fischer.parkerCoordinateAction_one

#print axioms Atlas.Fischer.parkerCoordinateAction_mul

#print axioms Atlas.Fischer.parkerCoordinateAction_eq_one

#print axioms Atlas.Fischer.parkerCoordinateAction_product

#print axioms Atlas.Fischer.parkerOctadProductDisjoint_action

#print axioms Atlas.Fischer.product_signed_sections_four

#print axioms Atlas.Fischer.product_signed_sections_disjoint

#print axioms Atlas.Fischer.product_signed_sections_two

#print axioms Atlas.Fischer.scalarParityAut_unique

#print axioms Atlas.Fischer.semilinearAlgebraParity_unique

#print axioms Atlas.Fischer.linearAlgebraAutomorphisms_iff

#print axioms Atlas.Fischer.parkerAlgebraRepresentation_injective

#print axioms Atlas.Fischer.parkerAlgebraRepresentation_parity

#print axioms Atlas.Fischer.scalarAlgebraRepresentation_injective

#print axioms Atlas.Fischer.scalarAlgebraRepresentation_parity

#print axioms Atlas.Fischer.cubic_add_first

#print axioms Atlas.Fischer.cubic_add_second

#print axioms Atlas.Fischer.cubic_add_third

#print axioms Atlas.Fischer.cubic_smul_first

#print axioms Atlas.Fischer.cubic_smul_second

#print axioms Atlas.Fischer.cubic_smul_third

#print axioms Atlas.Fischer.hermitian_smul_left

#print axioms Atlas.Fischer.hermitian_smul_right

#print axioms Atlas.Fischer.hermitian_star

#print axioms Atlas.Fischer.cocodePairing_coordinate

#print axioms Atlas.Fischer.coordinateCocode_parity

#print axioms Atlas.Fischer.coordinateCocode_sum

#print axioms Atlas.Fischer.coordinateCocode_sum_eq_zero

#print axioms Atlas.Fischer.coordinateCocode_representation

#print axioms Atlas.Fischer.coordinateCocode_generate

#print axioms Atlas.Fischer.octad_intersection_moment_levels

#print axioms Atlas.Fischer.octadIntersectionCount_eight

#print axioms Atlas.Fischer.octad_distribution_equations

#print axioms Atlas.Fischer.octad_intersection_distribution

#print axioms Atlas.Fischer.octad_outside_point_distribution

#print axioms Atlas.Fischer.octad_outside_duad_distribution

#print axioms Atlas.Fischer.octad_inside_duad_distribution

#print axioms Atlas.Fischer.octad_meets_duad_once

#print axioms Atlas.Fischer.octad_duad_distribution

#print axioms Atlas.Fischer.parkerRightLoopAction_mul

#print axioms Atlas.Fischer.parkerRightCoordinateAction_mul

#print axioms Atlas.Fischer.parkerStandardParity_inv

#print axioms Atlas.Fischer.parkerRightCoordinateAction_u

#print axioms Atlas.Fischer.parkerRightCoordinateAction_product

#print axioms Atlas.Fischer.ConwayParker.dimension

#print axioms Atlas.Fischer.ConwayParker.cocode_order

#print axioms Atlas.Fischer.ConwayParker.standard_order

#print axioms Atlas.Fischer.ConwayParker.standard_plus_order

#print axioms Atlas.Fischer.ConwayParker.scalar_phase_order

#print axioms Atlas.Fischer.ConwayParker.product_commutative

#print axioms Atlas.Fischer.ConwayParker.product_conjugate_left

#print axioms Atlas.Fischer.ConwayParker.product_conjugate_right

#print axioms Atlas.Fischer.ConwayParker.standard_preserves_product

#print axioms Atlas.Fischer.ConwayParker.standard_embedding_injective

#print axioms Atlas.Fischer.ConwayParker.scalar_embedding_injective

#print axioms Atlas.Fischer.ConwayParker.basic_root

#print axioms Atlas.Fischer.ConwayParker.basic_reflection_involutive

#print axioms Atlas.Fischer.ConwayParker.basic_reflection_antiunitary

#print axioms Atlas.Fischer.ConwayParker.basic_reflecting_root

#print axioms Atlas.Algebra.BinaryWalshCompatible

#print axioms Atlas.Algebra.binaryWalsh

#print axioms Atlas.Algebra.binaryWalshChar

#print axioms Atlas.Algebra.binaryWalshChar_apply

#print axioms Atlas.Algebra.binaryWalshChar_eq_zero

#print axioms Atlas.Algebra.binaryWalshChar_sum

#print axioms Atlas.Algebra.binaryWalshPolarRank

#print axioms Atlas.Algebra.binaryWalshRadical

#print axioms Atlas.Algebra.binaryWalshRadicalChar

#print axioms Atlas.Algebra.binaryWalshRadicalChar_eq_zero

#print axioms Atlas.Algebra.binaryWalshRadical_card

#print axioms Atlas.Algebra.binaryWalshRadical_finrank

#print axioms Atlas.Algebra.binaryWalshSign

#print axioms Atlas.Algebra.binaryWalshSign_add

#print axioms Atlas.Algebra.binaryWalshSign_eq_one

#print axioms Atlas.Algebra.binaryWalshSign_one

#print axioms Atlas.Algebra.binaryWalshSign_sq

#print axioms Atlas.Algebra.binaryWalshSign_zero

#print axioms Atlas.Algebra.binaryWalsh_add_constant

#print axioms Atlas.Algebra.binaryWalsh_eq_zero_of_not_compatible

#print axioms Atlas.Algebra.binaryWalsh_mem_radical

#print axioms Atlas.Algebra.binaryWalsh_phase_polar

#print axioms Atlas.Algebra.binaryWalsh_polar_formula

#print axioms Atlas.Algebra.binaryWalsh_polar_sum

#print axioms Atlas.Algebra.binaryWalsh_quadratic_add

#print axioms Atlas.Algebra.binaryWalsh_quadratic_zero

#print axioms Atlas.Algebra.binaryWalsh_rank_four_values

#print axioms Atlas.Algebra.binaryWalsh_rank_two_values

#print axioms Atlas.Algebra.binaryWalsh_rank_zero_values

#print axioms Atlas.Algebra.binaryWalsh_shift_product

#print axioms Atlas.Algebra.binaryWalsh_sq

#print axioms Atlas.Algebra.binaryWalsh_sq_of_compatible

#print axioms Atlas.Algebra.binaryWalsh_sq_radical_sum

#print axioms Atlas.Algebra.binaryWalsh_translate_polar

#print axioms Atlas.Fischer.OctadCalibration

#print axioms Atlas.Fischer.OctadShortenedHyperplane

#print axioms Atlas.Fischer.OctadicCharacter

#print axioms Atlas.Fischer.RootMapAntiunitaryOn

#print axioms Atlas.Fischer.axisBasisProduct_octad_total

#print axioms Atlas.Fischer.calibratedHyperplaneConvolutionTerm

#print axioms Atlas.Fischer.calibratedHyperplaneConvolution_local

#print axioms Atlas.Fischer.calibratedHyperplaneConvolution_sum

#print axioms Atlas.Fischer.calibratedHyperplaneLift

#print axioms Atlas.Fischer.calibratedHyperplaneLift_transport

#print axioms Atlas.Fischer.calibratedHyperplaneSupport_disjoint

#print axioms Atlas.Fischer.calibratedHyperplaneSupport_injective

#print axioms Atlas.Fischer.calibratedHyperplaneSupport_mem

#print axioms Atlas.Fischer.calibratedHyperplaneSupport_ne_octad

#print axioms Atlas.Fischer.calibratedHyperplaneVector

#print axioms Atlas.Fischer.calibratedHyperplaneVector_at_octad

#print axioms Atlas.Fischer.calibratedHyperplaneVector_at_support

#print axioms Atlas.Fischer.calibratedHyperplaneVector_change

#print axioms Atlas.Fischer.calibratedHyperplaneVector_norm

#print axioms Atlas.Fischer.calibratedHyperplaneVector_orthonormal

#print axioms Atlas.Fischer.calibratedHyperplaneVector_sum_complement

#print axioms Atlas.Fischer.calibratedHyperplane_diagonal_sum

#print axioms Atlas.Fischer.calibratedOctadVector_change

#print axioms Atlas.Fischer.chosenOctadCalibration

#print axioms Atlas.Fischer.cocodePairing_octadComplement

#print axioms Atlas.Fischer.exists_octad_calibrated_section

#print axioms Atlas.Fischer.hermitian_octadAxisSum_signedOctad

#print axioms Atlas.Fischer.hermitian_octadAxisSum_u

#print axioms Atlas.Fischer.hermitian_octad_calibratedHyperplane

#print axioms Atlas.Fischer.hermitian_octad_hyperplanePart

#print axioms Atlas.Fischer.hermitian_octadicAxis_hyperplanePart

#print axioms Atlas.Fischer.hermitian_octadicAxis_signedOctad

#print axioms Atlas.Fischer.hermitian_octadicRoot_calibratedOctad

#print axioms Atlas.Fischer.hermitian_octadicRoot_hyperplane

#print axioms Atlas.Fischer.hermitian_octadicRoot_u

#print axioms Atlas.Fischer.hermitian_orthonormal_sum

#print axioms Atlas.Fischer.hermitian_signedOctad_octadAxisSum

#print axioms Atlas.Fischer.hermitian_signedOctad_u

#print axioms Atlas.Fischer.hermitian_sum_left

#print axioms Atlas.Fischer.hermitian_sum_right

#print axioms Atlas.Fischer.hermitian_u_octadAxisSum

#print axioms Atlas.Fischer.hermitian_u_signedOctad

#print axioms Atlas.Fischer.hermitian_zero_left

#print axioms Atlas.Fischer.hermitian_zero_right

#print axioms Atlas.Fischer.mathieuFiveFixerComplement_kernel

#print axioms Atlas.Fischer.mathieuFiveFixer_stabilizes_octad

#print axioms Atlas.Fischer.mathieuOctadComplementHom_ker

#print axioms Atlas.Fischer.mathieuOctadComplementHom_surjective

#print axioms Atlas.Fischer.mathieuOctadFive_quotient_order

#print axioms Atlas.Fischer.mathieuOctadMarkedLocal_iff

#print axioms Atlas.Fischer.mathieuOctadMarked_perfect_quotient

#print axioms Atlas.Fischer.mathieuOctadRestrictedHom_surjective

#print axioms Atlas.Fischer.mathieuTranslationGenerated_eq_fixing

#print axioms Atlas.Fischer.mathieuTranslationGenerated_eq_fixing_of_octad

#print axioms Atlas.Fischer.mathieuTranslationGenerated_factorization

#print axioms Atlas.Fischer.mathieuTranslationGenerated_match

#print axioms Atlas.Fischer.mathieuTranslationGenerated_multipleTransitive

#print axioms Atlas.Fischer.mathieuTranslationNormalSubgroup_normal

#print axioms Atlas.Fischer.mem_octadCocodeAnnihilator

#print axioms Atlas.Fischer.octadAffineWord_formula

#print axioms Atlas.Fischer.octadAffineWord_mem

#print axioms Atlas.Fischer.octadAffineWord_range

#print axioms Atlas.Fischer.octadAnnihilator_commutes_rootMap

#print axioms Atlas.Fischer.octadAnnihilator_fixes_root

#print axioms Atlas.Fischer.octadAxisSum

#print axioms Atlas.Fischer.octadAxisSum_add_exterior

#print axioms Atlas.Fischer.octadAxisSum_norm

#print axioms Atlas.Fischer.octadCalibratedSection_card

#print axioms Atlas.Fischer.octadCalibratedSection_spec

#print axioms Atlas.Fischer.octadCalibrationDifference

#print axioms Atlas.Fischer.octadCalibrationTransport

#print axioms Atlas.Fischer.octadCharacterTranslation_add

#print axioms Atlas.Fischer.octadCharacterTranslation_coordinates

#print axioms Atlas.Fischer.octadCharacterTranslation_regular

#print axioms Atlas.Fischer.octadCharacterTranslation_word

#print axioms Atlas.Fischer.octadCharacterTranslation_zero

#print axioms Atlas.Fischer.octadCharacters_card

#print axioms Atlas.Fischer.octadCocodeAnnihilator_card

#print axioms Atlas.Fischer.octadCocodeAnnihilator_finrank

#print axioms Atlas.Fischer.octadCocodeRestriction_surjective

#print axioms Atlas.Fischer.octadEvaluation_hyperplane_sign_pair_sum

#print axioms Atlas.Fischer.octadEvaluation_range

#print axioms Atlas.Fischer.octadEvaluation_sign_pair_sum

#print axioms Atlas.Fischer.octadExteriorAxisSum

#print axioms Atlas.Fischer.octadHyperplaneTransport

#print axioms Atlas.Fischer.octadHyperplaneTransport_val

#print axioms Atlas.Fischer.octadHyperplane_local_convolution

#print axioms Atlas.Fischer.octadLabelCharacter_independent

#print axioms Atlas.Fischer.octadLabelCharacter_restriction

#print axioms Atlas.Fischer.octadMarkedPoints_card

#print axioms Atlas.Fischer.octadParkerPreimage_card

#print axioms Atlas.Fischer.octadParkerSection_card

#print axioms Atlas.Fischer.octadPointwiseEmbedding_range

#print axioms Atlas.Fischer.octadRationalProjection_coordinate

#print axioms Atlas.Fischer.octadRationalProjection_eq_self

#print axioms Atlas.Fischer.octadRationalProjection_mem

#print axioms Atlas.Fischer.octadRationalProjection_other

#print axioms Atlas.Fischer.octadRationalProjection_sum

#print axioms Atlas.Fischer.octadRealGrade_dimension

#print axioms Atlas.Fischer.octadRealGrade_duad_dimension

#print axioms Atlas.Fischer.octadRealGrade_empty_dimension

#print axioms Atlas.Fischer.octadRealGrade_finrank

#print axioms Atlas.Fischer.octadRealGrade_full_dimension

#print axioms Atlas.Fischer.octadRealGrade_six_dimension

#print axioms Atlas.Fischer.octadRealGrade_tetrad_dimension

#print axioms Atlas.Fischer.octadRealGrade_tmul

#print axioms Atlas.Fischer.octadReplication_avoidance_bound

#print axioms Atlas.Fischer.octadShortenedCode_card

#print axioms Atlas.Fischer.octadShortenedHyperplane_weight

#print axioms Atlas.Fischer.octadTranslationGenerators_conj

#print axioms Atlas.Fischer.octadUnmarkedPoints_card

#print axioms Atlas.Fischer.octadWord_not_shortened

#print axioms Atlas.Fischer.octad_contains_avoids_two

#print axioms Atlas.Fischer.octad_translation_align

#print axioms Atlas.Fischer.octadicAxisPart

#print axioms Atlas.Fischer.octadicAxisPart_axis_apply

#print axioms Atlas.Fischer.octadicAxisPart_eq

#print axioms Atlas.Fischer.octadicAxisPart_norm

#print axioms Atlas.Fischer.octadicAxisPart_octad_apply

#print axioms Atlas.Fischer.octadicCharacterTransport_apply

#print axioms Atlas.Fischer.octadicCharacterTransport_one

#print axioms Atlas.Fischer.octadicHyperplaneAxisSum

#print axioms Atlas.Fischer.octadicHyperplanePart

#print axioms Atlas.Fischer.octadicHyperplanePart_norm

#print axioms Atlas.Fischer.octadicHyperplanePart_zero

#print axioms Atlas.Fischer.octadicNineGenerators

#print axioms Atlas.Fischer.octadicNineSpace

#print axioms Atlas.Fischer.octadicRoot

#print axioms Atlas.Fischer.octadicRootFibre

#print axioms Atlas.Fischer.octadicRootFibre_card

#print axioms Atlas.Fischer.octadicRootFibre_choice_independent

#print axioms Atlas.Fischer.octadicRoot_H_transitive

#print axioms Atlas.Fischer.octadicRoot_axis_coefficient

#print axioms Atlas.Fischer.octadicRoot_change

#print axioms Atlas.Fischer.octadicRoot_cocode_transitive

#print axioms Atlas.Fischer.octadicRoot_hyperplane_coefficient

#print axioms Atlas.Fischer.octadicRoot_injective

#print axioms Atlas.Fischer.octadicRoot_isRoot

#print axioms Atlas.Fischer.octadicRoot_norm

#print axioms Atlas.Fischer.octadicRoot_norm_formula

#print axioms Atlas.Fischer.octadicRoot_octad_coefficient

#print axioms Atlas.Fischer.octadicRoot_zero_formula

#print axioms Atlas.Fischer.octadicThetaPart_norm

#print axioms Atlas.Fischer.parkerCocodeAction_calibratedHyperplane

#print axioms Atlas.Fischer.parkerCocodeAction_octadicAxisPart

#print axioms Atlas.Fischer.parkerCocodeAction_octadicRoot

#print axioms Atlas.Fischer.parkerCocodeAction_signedOctad

#print axioms Atlas.Fischer.parkerCocodeAction_smul

#print axioms Atlas.Fischer.parkerCoordinateAction_calibratedHyperplane

#print axioms Atlas.Fischer.parkerCoordinateAction_octadicAxisPart

#print axioms Atlas.Fischer.parkerCoordinateAction_octadicHyperplanePart

#print axioms Atlas.Fischer.parkerCoordinateAction_octadicRoot

#print axioms Atlas.Fischer.parkerCoordinateAction_rootMap

#print axioms Atlas.Fischer.parkerOctadAction_transitive

#print axioms Atlas.Fischer.parkerScalarSign_injective

#print axioms Atlas.Fischer.parkerScalarSign_ne_zero

#print axioms Atlas.Fischer.parkerScalarSign_sum

#print axioms Atlas.Fischer.parkerScalarSign_walsh

#print axioms Atlas.Fischer.product_axisSum_octadAxisSum

#print axioms Atlas.Fischer.product_calibratedHyperplane_diagonal_formula

#print axioms Atlas.Fischer.product_calibratedHyperplane_hyperplanePart

#print axioms Atlas.Fischer.product_calibratedHyperplane_self

#print axioms Atlas.Fischer.product_calibratedHyperplanes_partition

#print axioms Atlas.Fischer.product_calibratedOctad_hyperplanePart

#print axioms Atlas.Fischer.product_calibratedOctad_self

#print axioms Atlas.Fischer.product_octadAxisSum_self

#print axioms Atlas.Fischer.product_octadAxisSum_xOctad

#print axioms Atlas.Fischer.product_octadAxisSum_xOctad_disjoint

#print axioms Atlas.Fischer.product_octadicAxisPart_hyperplane

#print axioms Atlas.Fischer.product_octadicAxisPart_hyperplanePart

#print axioms Atlas.Fischer.product_octadicAxisPart_octad

#print axioms Atlas.Fischer.product_octadicAxisPart_self

#print axioms Atlas.Fischer.product_octadicAxisPart_theta_octad

#print axioms Atlas.Fischer.product_octadicHyperplanePart_self

#print axioms Atlas.Fischer.product_octadicRoot

#print axioms Atlas.Fischer.product_octadicRoot_zero

#print axioms Atlas.Fischer.product_theta_calibratedOctad_self

#print axioms Atlas.Fischer.product_theta_octad_hyperplanePart

#print axioms Atlas.Fischer.product_u_calibratedHyperplane

#print axioms Atlas.Fischer.product_u_calibratedOctad

#print axioms Atlas.Fischer.product_u_hyperplanePart_inside

#print axioms Atlas.Fischer.product_u_hyperplanePart_outside

#print axioms Atlas.Fischer.product_u_octadAxisSum_inside

#print axioms Atlas.Fischer.product_u_octadAxisSum_outside

#print axioms Atlas.Fischer.product_u_octadicAxis_inside

#print axioms Atlas.Fischer.product_u_octadicAxis_outside

#print axioms Atlas.Fischer.rational_real_extension_injective

#print axioms Atlas.Fischer.realCoordinateEquiv_tmul

#print axioms Atlas.Fischer.realCoordinates_finrank

#print axioms Atlas.Fischer.rootMap_antiunitary_span

#print axioms Atlas.Fischer.rootMap_hermitian_symmetric

#print axioms Atlas.Fischer.rootMap_invariant_span

#print axioms Atlas.Fischer.rootMap_involutive_of_antiunitary

#print axioms Atlas.Fischer.rootMap_involutive_on_of_antiunitaryOn

#print axioms Atlas.Fischer.rootMap_octadic_hyperplane

#print axioms Atlas.Fischer.rootMap_octadic_inside_axis

#print axioms Atlas.Fischer.rootMap_octadic_inside_octad_pairing

#print axioms Atlas.Fischer.rootMap_octadic_inside_pairing

#print axioms Atlas.Fischer.rootMap_octadic_nine_antiunitary

#print axioms Atlas.Fischer.rootMap_octadic_nine_invariant

#print axioms Atlas.Fischer.rootMap_octadic_nine_involutive

#print axioms Atlas.Fischer.rootMap_octadic_octad

#print axioms Atlas.Fischer.rootMap_octadic_octadAxisSum

#print axioms Atlas.Fischer.rootMap_octadic_octad_norm

#print axioms Atlas.Fischer.rootMap_octadic_outside_axis

#print axioms Atlas.Fischer.rootMap_sum

#print axioms Atlas.Fischer.rootMap_zero

#print axioms Atlas.Fischer.theta_half_smul_octadicRoot

#print axioms Atlas.Fischer.theta_ne_zero

#print axioms Atlas.GroupTheory.finite_partial_match

#print axioms Atlas.GroupTheory.hom_trivial_of_perfect_quotient

#print axioms Atlas.GroupTheory.normal_eq_top_of_local_quotients

#print axioms Atlas.Fischer.octadicRoot_reflection_package
#print axioms Atlas.Fischer.octadicReflection_hermitian
#print axioms Atlas.Fischer.octadicReflection_involutive
#print axioms Atlas.Fischer.octadQuadraticIsometry
#print axioms Atlas.Fischer.octadRealGrade_product
#print axioms Atlas.Fischer.octadicBlock_dimension_total

#print axioms Atlas.Fischer.coordinateCubicSlice_eq
#print axioms Atlas.Fischer.productTrace_eq_hermitian
#print axioms Atlas.Fischer.coordinateCubicNorm_eq
#print axioms Atlas.Fischer.semilinearAlgebraAutomorphism_hermitian
#print axioms Atlas.Fischer.coordinateQuintic_parker
#print axioms Atlas.Fischer.coordinateQuintic_nonzero_seven_types
#print axioms Atlas.Fischer.coordinateQuintic_theta_phase
#print axioms Atlas.Fischer.normalizedCoordinateQuintic_eq

#print axioms Atlas.Fischer.coordinateQuintic_points
#print axioms Atlas.Fischer.coordinateQuintic_points_blocks
#print axioms Atlas.Fischer.quinticPointUUU_value
#print axioms Atlas.Fischer.quinticPointUWW_three
#print axioms Atlas.Fischer.quinticPointWWW_incidence
#print axioms Atlas.Fischer.cubicSextetIncidenceSum_distinct
#print axioms Atlas.Fischer.cubicTrioIncidenceSum_distinct

#print axioms Atlas.Fischer.parkerGolayFactorSet_interchange
#print axioms Atlas.Fischer.parkerOmegaFactorSet_octad_quadrilateral
#print axioms Atlas.Fischer.cubicOctadQuadrilateralWeight_formula
#print axioms Atlas.Fischer.octad_contraction_exponent
#print axioms Atlas.Fischer.coordinateQuinticCubicProduct_octad_weight

#print axioms Atlas.Fischer.coordinateQuintic_point_octads
#print axioms Atlas.Fischer.coordinateQuintic_octad_point_octad
#print axioms Atlas.Fischer.coordinateQuintic_octads_point
#print axioms Atlas.Fischer.cubicQuadrilateral_point_sum
#print axioms Atlas.Fischer.quinticOctad_C0_sextet
#print axioms Atlas.Fischer.quinticOctad_C0_trio
#print axioms Atlas.Fischer.coordinateQuintic_sextet_reduced
#print axioms Atlas.Fischer.coordinateQuintic_trio_reduced

#print axioms Atlas.Fischer.countingCanonicalSextet_signed_sum
#print axioms Atlas.Fischer.countingCanonicalTrio_signed_sum
#print axioms Atlas.Fischer.coordinateQuintic_eq_1002_coordinateCubic

#print axioms Atlas.Fischer.rootMap_algebra_criterion
#print axioms Atlas.Fischer.octadicReflection_product
#print axioms Atlas.Fischer.octadicRoot_phase_isReflectingRoot
#print axioms Atlas.Fischer.octadicPhaseAlgebraAutomorphism_square
#print axioms Atlas.Fischer.octadicPhaseAlgebraAutomorphism_parity

#print axioms Atlas.Algebra.hermitian_cube_root_quadratic_bound
#print axioms Atlas.Fischer.rootRay_card
#print axioms Atlas.Fischer.reflectingRoot_pairing_zero_or_mu3
#print axioms Atlas.Fischer.reflectingRoot_finite_family_bound
#print axioms Atlas.Fischer.reflectingRoot_symmetric_squares_independent

#print axioms Atlas.Fischer.duadCharacterProduct_coordinate_formula
#print axioms Atlas.Fischer.duadCharacterProduct_injective
#print axioms Atlas.Fischer.duadProductFibre_card
#print axioms Atlas.Fischer.duadProductFibre_cocode_kernel_card
#print axioms Atlas.Fischer.duadCoordinateWord_span

#print axioms Atlas.Fischer.displayedReflectingRay_card
#print axioms Atlas.Fischer.basicReflectingRay_card
#print axioms Atlas.Fischer.octadicReflectingRay_card
#print axioms Atlas.Fischer.duadicReflectingRay_card
#print axioms Atlas.Fischer.hermitian_basicAxis_octadic
#print axioms Atlas.Fischer.hermitian_basicAxis_duadic

#print axioms Atlas.Fischer.reflectingRootParameter_exhaust
#print axioms Atlas.Fischer.duadProductFibre_choice_independent
#print axioms Atlas.Fischer.reflectingFamily_second_moment
#print axioms Atlas.Fischer.reflectingFamily_third_moment
#print axioms Atlas.Fischer.reflectingFamily_product_unique
#print axioms Atlas.Fischer.reflectingFamilyComplexSquareBasis
#print axioms Atlas.Fischer.reflectingFamily_rayPermutation_criterion
#print axioms Atlas.Fischer.reflectingFamily_nonzero_valency
#print axioms Atlas.Fischer.reflectingFamily_zero_valency
#print axioms Atlas.Fischer.reflectingFamily_zero_graph_connected

#print axioms Atlas.Fischer.rootGeneratedRayGroup_transitive
#print axioms Atlas.Fischer.displayedRootRayInvolution_injective
#print axioms Atlas.Fischer.distinguishedRootElement_product_order
#print axioms Atlas.Fischer.semilinearRayKernel_eq_scalar_range
#print axioms Atlas.Fischer.semilinearAlgebraAutomorphism_finite
#print axioms Atlas.Fischer.scalarAlgebraRepresentation_range_le_generated
#print axioms Atlas.Fischer.rootGeneratedAlgebra_commutator
#print axioms Atlas.Fischer.rootGeneratedRay_commutator
#print axioms Atlas.Fischer.rootGeneratedAlgebraParity_kernel_perfect
#print axioms Atlas.Fischer.rootGeneratedRayParity_kernel_perfect
#print axioms Atlas.Fischer.rootGeneratedPositiveProjection_kernel_card
#print axioms Atlas.Fischer.rootGeneratedPositiveProjection_nonsplit
#print axioms Atlas.Fischer.cocodeRayHom_relations
#print axioms Atlas.Fischer.cocodeRayHom_range_card

#print axioms Atlas.Fischer.pointwiseAxis_unique_cocode
#print axioms Atlas.Fischer.basicFrame_scalar_golay
#print axioms Atlas.Fischer.mem_basicFrameStabilizer_iff_scalar_parker
#print axioms Atlas.Fischer.basicFrameStabilizer_order
#print axioms Atlas.Fischer.rootGeneratedRay_normal_pgroup_eq_bot
#print axioms Atlas.Fischer.rootGeneratedRay_solvable_normal_eq_bot

#print axioms Atlas.Fischer.rootGenerated_basicFrame_nontrivial
#print axioms Atlas.Fischer.generatedFrameMathieuImage_eq_top
#print axioms Atlas.Fischer.basicFrameStabilizer_le_generated
#print axioms Atlas.Fischer.fischerFrames_conjugate
#print axioms Atlas.Fischer.fischerFrame_card
#print axioms Atlas.Fischer.commutingTuples_homogeneous
#print axioms Atlas.Fischer.rootGeneratedAlgebraGroup_eq_top
#print axioms Atlas.Fischer.fullSemilinearScalarQuotientEquiv
#print axioms Atlas.Fischer.commutingExtension_card
#print axioms Atlas.Fischer.orderedCommutingPentad_card
#print axioms Atlas.Fischer.orderedCommutingTuple_order_product
#print axioms Atlas.Fischer.parkerRayHom_range
#print axioms Atlas.Fischer.markedFrameRayStabilizer_five_order

#print axioms Atlas.Fischer.commutingPentadFrame_card
#print axioms Atlas.Fischer.commutingPentadFrame_transitive
#print axioms Atlas.Fischer.basicFramePointwiseRayStabilizer_ambient
#print axioms Atlas.Fischer.markedPentadPointwise_order
#print axioms Atlas.Fischer.rootGeneratedRayGroup_order_factored
#print axioms Atlas.Fischer.rootGeneratedRayGroup_order_value
#print axioms Atlas.Fischer.fischerFrame_count
#print axioms Atlas.Sporadic.Fischer24.card
#print axioms Atlas.Sporadic.Fischer24.not_simple
#print axioms Atlas.Sporadic.Fischer24.positive_perfect
#print axioms Atlas.Sporadic.Fischer24.positive_transitive
#print axioms Atlas.Sporadic.Fischer24.construction
#print axioms Atlas.Sporadic.Fischer24.exists_model

-- Job26 actual residue models, exact kernels, orders and full generation.
#print axioms Atlas.Fischer.residueConjugationHom_kernel
#print axioms Atlas.Fischer.residueGroup_singleton_order
#print axioms Atlas.Fischer.residueGroup_pair_order
#print axioms Atlas.Fischer.residueGroup_faithful
#print axioms Atlas.Fischer.residueGroup_transitive
#print axioms Atlas.Fischer.residueQuotientTransport_equivariant
#print axioms Atlas.Fischer.residueGenerated_eq_centralizer
#print axioms Atlas.Fischer.residueDistinguishedElement_generates

-- Job26: the three actual Fischer simple groups and their public constructions.
#print axioms Atlas.Fischer.residueGroup_primitive
#print axioms Atlas.Fischer.rootGeneratedRayGroup_primitive
#print axioms Atlas.Fischer.residueDistinguished_injective
#print axioms Atlas.Fischer.residueDistinguished_product_order
#print axioms Atlas.Sporadic.Fischer24Prime.card
#print axioms Atlas.Sporadic.Fischer24Prime.simple
#print axioms Atlas.Sporadic.Fischer24Prime.noncommutative
#print axioms Atlas.Sporadic.Fischer24Prime.construction
#print axioms Atlas.Sporadic.Fischer24Prime.exists_model
#print axioms Atlas.Sporadic.Fischer23.card
#print axioms Atlas.Sporadic.Fischer23.simple
#print axioms Atlas.Sporadic.Fischer23.noncommutative
#print axioms Atlas.Sporadic.Fischer23.construction
#print axioms Atlas.Sporadic.Fischer23.exists_model
#print axioms Atlas.Sporadic.Fischer22.card
#print axioms Atlas.Sporadic.Fischer22.simple
#print axioms Atlas.Sporadic.Fischer22.noncommutative
#print axioms Atlas.Sporadic.Fischer22.construction
#print axioms Atlas.Sporadic.Fischer22.exists_model
#print axioms Atlas.Fischer.DistinguishedDoubleCover
#print axioms Atlas.Fischer.DistinguishedResidue
#print axioms Atlas.Fischer.DoubleCover22.Construction
#print axioms Atlas.Fischer.DoubleCover22.Model
#print axioms Atlas.Fischer.DoubleCover22.ModelAt
#print axioms Atlas.Fischer.DoubleCover22.Points
#print axioms Atlas.Fischer.DoubleCover22.Target
#print axioms Atlas.Fischer.DoubleCover22.card
#print axioms Atlas.Fischer.DoubleCover22.card_at
#print axioms Atlas.Fischer.DoubleCover22.center
#print axioms Atlas.Fischer.DoubleCover22.centralInvolution
#print axioms Atlas.Fischer.DoubleCover22.centralInvolution_order
#print axioms Atlas.Fischer.DoubleCover22.centralizerEquiv
#print axioms Atlas.Fischer.DoubleCover22.construction
#print axioms Atlas.Fischer.DoubleCover22.faithful
#print axioms Atlas.Fischer.DoubleCover22.finite
#print axioms Atlas.Fischer.DoubleCover22.kernel
#print axioms Atlas.Fischer.DoubleCover22.kernel_card
#print axioms Atlas.Fischer.DoubleCover22.nonsplit
#print axioms Atlas.Fischer.DoubleCover22.originalAction
#print axioms Atlas.Fischer.DoubleCover22.perfect
#print axioms Atlas.Fischer.DoubleCover22.perfect_at
#print axioms Atlas.Fischer.DoubleCover22.projection
#print axioms Atlas.Fischer.DoubleCover22.projection_surjective
#print axioms Atlas.Fischer.DoubleCover22.relative_card
#print axioms Atlas.Fischer.FischerDoubleCover
#print axioms Atlas.Fischer.distinguishedCentralKernel
#print axioms Atlas.Fischer.distinguishedCentralKernelTransport
#print axioms Atlas.Fischer.distinguishedCentralKernel_normal
#print axioms Atlas.Fischer.distinguishedCentralKernel_transport
#print axioms Atlas.Fischer.distinguishedCentralizer
#print axioms Atlas.Fischer.distinguishedCentralizerDirectProduct
#print axioms Atlas.Fischer.distinguishedCentralizerParity
#print axioms Atlas.Fischer.distinguishedCentralizerTransport
#print axioms Atlas.Fischer.distinguishedCentralizerTransport_parity
#print axioms Atlas.Fischer.distinguishedCentralizerTransport_val
#print axioms Atlas.Fischer.distinguishedCentralizer_structure
#print axioms Atlas.Fischer.distinguishedDoubleCoverTransport
#print axioms Atlas.Fischer.distinguishedDoubleCoverTransport_mk
#print axioms Atlas.Fischer.distinguishedDoubleCover_structure
#print axioms Atlas.Fischer.distinguishedEvenCentralizerEquiv
#print axioms Atlas.Fischer.distinguishedEvenKernelTransport
#print axioms Atlas.Fischer.distinguishedEvenKernel_transport
#print axioms Atlas.Fischer.distinguishedEvenSection
#print axioms Atlas.Fischer.distinguishedEvenSection_action
#print axioms Atlas.Fischer.distinguishedEvenSection_conjugate
#print axioms Atlas.Fischer.distinguishedEvenSection_even
#print axioms Atlas.Fischer.distinguishedEvenSection_odd
#print axioms Atlas.Fischer.distinguishedPairCentralizer
#print axioms Atlas.Fischer.distinguishedPairCentralizerTransport
#print axioms Atlas.Fischer.distinguishedPairCentralizerTransport_val
#print axioms Atlas.Fischer.distinguishedPairFirstKernel
#print axioms Atlas.Fischer.distinguishedPairFirstKernel_normal
#print axioms Atlas.Fischer.distinguishedPairFirstKernel_transport
#print axioms Atlas.Fischer.distinguishedPositiveCentralizer
#print axioms Atlas.Fischer.distinguishedResiduePositiveEquiv
#print axioms Atlas.Fischer.distinguishedResidueTransport
#print axioms Atlas.Fischer.distinguished_conjugate_basic
#print axioms Atlas.Fischer.distinguished_pair_into_basic
#print axioms Atlas.Fischer.doubleCentralizerFirstKernel
#print axioms Atlas.Fischer.doubleCentralizerFirstKernel_card
#print axioms Atlas.Fischer.doubleCentralizerFirstKernel_central
#print axioms Atlas.Fischer.doubleCentralizerFirstKernel_le
#print axioms Atlas.Fischer.doubleCentralizerInclusion
#print axioms Atlas.Fischer.doubleCentralizerTargetHom
#print axioms Atlas.Fischer.doubleCentralizerTargetHom_kernel
#print axioms Atlas.Fischer.doubleCentralizerTargetHom_surjective
#print axioms Atlas.Fischer.doubleCentralizer_lift_iff
#print axioms Atlas.Fischer.doubleCoverCentralizerEquiv
#print axioms Atlas.Fischer.doubleCoverCentralizerTarget
#print axioms Atlas.Fischer.doubleCoverFirstKernel_transport
#print axioms Atlas.Fischer.doubleCoverMarkedElement
#print axioms Atlas.Fischer.doubleCoverMarkedElement_first
#print axioms Atlas.Fischer.doubleCoverMarkedElement_second_order
#print axioms Atlas.Fischer.doubleCoverMarkedElement_square
#print axioms Atlas.Fischer.doubleCoverOriginalAction
#print axioms Atlas.Fischer.doubleCoverOriginalAction_faithful
#print axioms Atlas.Fischer.doubleCoverOriginalAction_mk
#print axioms Atlas.Fischer.doubleCoverProjection
#print axioms Atlas.Fischer.doubleCoverProjection_kernel
#print axioms Atlas.Fischer.doubleCoverProjection_kernel_card
#print axioms Atlas.Fischer.doubleCoverProjection_kernel_central
#print axioms Atlas.Fischer.doubleCoverProjection_nonsplit
#print axioms Atlas.Fischer.doubleCoverProjection_second
#print axioms Atlas.Fischer.doubleCoverProjection_surjective
#print axioms Atlas.Fischer.doubleCoverResidualElement
#print axioms Atlas.Fischer.doubleCoverResidualElement_basic
#print axioms Atlas.Fischer.doubleCoverResidualElement_conjugate
#print axioms Atlas.Fischer.doubleCoverResidualElement_square
#print axioms Atlas.Fischer.doubleCoverSecondPoint
#print axioms Atlas.Fischer.doubleCoverTransport
#print axioms Atlas.Fischer.doubleCoverTransport_projection
#print axioms Atlas.Fischer.doubleCoverTransport_second
#print axioms Atlas.Fischer.doubleCover_center
#print axioms Atlas.Fischer.doubleCover_generators
#print axioms Atlas.Fischer.doubleCover_order
#print axioms Atlas.Fischer.doubleCover_pair_transport
#print axioms Atlas.Fischer.doubleCover_perfect
#print axioms Atlas.Fischer.firstCentralizerDirectProduct
#print axioms Atlas.Fischer.firstCentralizerEvenPart
#print axioms Atlas.Fischer.firstCentralizerEvenPart_action
#print axioms Atlas.Fischer.firstCentralizerEvenPart_even
#print axioms Atlas.Fischer.firstCentralizerEvenPart_kernel
#print axioms Atlas.Fischer.firstCentralizerEvenPart_odd
#print axioms Atlas.Fischer.firstCentralizerEvenPart_quotient
#print axioms Atlas.Fischer.firstCentralizerEvenPart_surjective
#print axioms Atlas.Fischer.firstCentralizerMarked
#print axioms Atlas.Fischer.firstCentralizerParity
#print axioms Atlas.Fischer.firstCentralizerParity_marked
#print axioms Atlas.Fischer.firstCentralizerParity_marked_bijective
#print axioms Atlas.Fischer.firstCentralizerProductEquiv
#print axioms Atlas.Fischer.firstElementary_le_doubleCentralizer
#print axioms Atlas.Fischer.firstEvenCentralizerEquiv
#print axioms Atlas.Fischer.firstPositiveCentralizer
#print axioms Atlas.Fischer.firstResidueEvenEquiv
#print axioms Atlas.Fischer.firstResidueEvenEquiv_mk
#print axioms Atlas.Fischer.firstResiduePositiveCentralizerEquiv
#print axioms Atlas.Fischer.firstResiduePositiveEmbedding
#print axioms Atlas.Fischer.firstResiduePositiveEmbedding_injective
#print axioms Atlas.GroupTheory.centralKernelProductEquiv
#print axioms Atlas.Fischer.SemilinearCover.card
#print axioms Atlas.Fischer.SemilinearCover.construction
#print axioms Atlas.Fischer.SemilinearCover.finite
#print axioms Atlas.Fischer.SemilinearCover.kernel
#print axioms Atlas.Fischer.SemilinearCover.kernel_card
#print axioms Atlas.Fischer.SemilinearCover.kernel_not_central
#print axioms Atlas.Fischer.SemilinearCover.odd_scalar_inversion
#print axioms Atlas.Fischer.SemilinearCover.order
#print axioms Atlas.Fischer.SemilinearCover.projection_surjective
#print axioms Atlas.Fischer.SemilinearCover.reflection_conjugate_linear
#print axioms Atlas.Fischer.SemilinearCover.reflection_order
#print axioms Atlas.Fischer.SemilinearCover.reflection_scalar_inversion
#print axioms Atlas.Fischer.SemilinearCover.scalarQuotientEquiv
#print axioms Atlas.Fischer.SemilinearCover.scalar_injective
#print axioms Atlas.Fischer.SemilinearCover.semidirectEquiv
#print axioms Atlas.Fischer.SemilinearCover.semidirect_apply
#print axioms Atlas.Fischer.TripleCover.card
#print axioms Atlas.Fischer.TripleCover.center
#print axioms Atlas.Fischer.TripleCover.center_card
#print axioms Atlas.Fischer.TripleCover.construction
#print axioms Atlas.Fischer.TripleCover.dimension
#print axioms Atlas.Fischer.TripleCover.finite
#print axioms Atlas.Fischer.TripleCover.kernel
#print axioms Atlas.Fischer.TripleCover.kernel_card
#print axioms Atlas.Fischer.TripleCover.linearRepresentation
#print axioms Atlas.Fischer.TripleCover.nonsplit
#print axioms Atlas.Fischer.TripleCover.order
#print axioms Atlas.Fischer.TripleCover.perfect
#print axioms Atlas.Fischer.TripleCover.projection_surjective
#print axioms Atlas.Fischer.TripleCover.quotient_faithful
#print axioms Atlas.Fischer.TripleCover.quotient_transitive
#print axioms Atlas.Fischer.TripleCover.representation_injective
#print axioms Atlas.Fischer.TripleCover.representation_product
#print axioms Atlas.Fischer.TripleCover.representation_scalar
#print axioms Atlas.Fischer.TripleCover.scalarQuotientEquiv
#print axioms Atlas.Fischer.TripleCover.scalar_injective
#print axioms Atlas.Fischer.displayedRayProjectiveDirection
#print axioms Atlas.Fischer.displayedRayProjectiveDirection_eq_mk
#print axioms Atlas.Fischer.displayedRayProjectiveDirection_equivariant
#print axioms Atlas.Fischer.displayedRayProjectiveDirection_injective
#print axioms Atlas.Fischer.displayedRayProjectiveDirection_lift_independent
#print axioms Atlas.Fischer.displayedRayRepresentative
#print axioms Atlas.Fischer.displayedRayRepresentative_ray
#print axioms Atlas.Fischer.displayedRayRepresentative_root
#print axioms Atlas.Fischer.displayedRoot_conjugate_linear
#print axioms Atlas.Fischer.displayedRoot_scalar_conjugation
#print axioms Atlas.Fischer.fullSemilinearAlgebra_order_triple
#print axioms Atlas.Fischer.fullSemilinearScalarKernel_not_central
#print axioms Atlas.Fischer.fullSemilinearSemidirectEquiv
#print axioms Atlas.Fischer.fullSemilinearSemidirectEquiv_apply
#print axioms Atlas.Fischer.oddSemilinear_scalar_conjugation
#print axioms Atlas.Fischer.positiveAlgebraLinearRepresentation
#print axioms Atlas.Fischer.positiveAlgebraLinearRepresentation_dimension
#print axioms Atlas.Fischer.positiveAlgebraLinearRepresentation_injective
#print axioms Atlas.Fischer.positiveAlgebraLinearRepresentation_product
#print axioms Atlas.Fischer.positiveAlgebraLinearRepresentation_scalar
#print axioms Atlas.Fischer.rootGeneratedAlgebraPositive_center
#print axioms Atlas.Fischer.rootGeneratedAlgebraPositive_order_triple
#print axioms Atlas.Fischer.rootGeneratedRayPositive_center
#print axioms Atlas.Fischer.rootReflectionComplement_order
#print axioms Atlas.Fischer.rootReflectionPositiveAction
#print axioms Atlas.Fischer.rootReflection_isComplement
#print axioms Atlas.Fischer.rootReflection_parity_restriction_bijective
#print axioms Atlas.Fischer.root_projective_eq_iff
#print axioms Atlas.Fischer.tripleCover_complex_coordinate_comparison
#print axioms Atlas.GroupTheory.isComplement_kernel_of_restriction_bijective
#print axioms Atlas.Sporadic.Fischer22.exists_mul_ne_mul
#print axioms Atlas.Sporadic.Fischer22.isSimpleGroup
#print axioms Atlas.Sporadic.Fischer23.exists_mul_ne_mul
#print axioms Atlas.Sporadic.Fischer23.isSimpleGroup
#print axioms Atlas.Sporadic.Fischer24.primitive
#print axioms Atlas.Sporadic.Fischer24.rankThreeActionComparison
#print axioms Atlas.Sporadic.Fischer24.rankThreeGroupComparison
#print axioms Atlas.Sporadic.Fischer24.rankThreePointComparison
#print axioms Atlas.Sporadic.Fischer24.rankThree_action_compatible
#print axioms Atlas.Sporadic.Fischer24.rank_three
#print axioms Atlas.Sporadic.Fischer24.subdegrees
#print axioms Atlas.Sporadic.Fischer24Prime.exists_mul_ne_mul
#print axioms Atlas.Sporadic.Fischer24Prime.isSimpleGroup
#print axioms Atlas.Fischer.binaryFourAffine_character_translation
#print axioms Atlas.Fischer.mathieuOctad_character_pointwise
#print axioms Atlas.Fischer.mathieuOctad_character_trivial
#print axioms Atlas.Fischer.parkerLoop_same_code_sign
#print axioms Atlas.Fischer.parkerOctadTriple_three
#print axioms Atlas.Fischer.parkerOctad_uniform_sign_impossible
#print axioms Atlas.Fischer.parkerSection_equivariant_octad_representatives
#print axioms Atlas.Fischer.parkerSection_fixes_octad
#print axioms Atlas.Fischer.parkerSection_octad_character
#print axioms Atlas.Fischer.parkerSection_octad_form
#print axioms Atlas.Fischer.parkerSection_octad_transport_unique
#print axioms Atlas.Fischer.parkerSection_uniform_octad_sign
#print axioms Atlas.Fischer.parkerStandardProjection_nonsplit

-- Symplectic-family foundations: no positive-rank order or simplicity claimed here.
#print axioms Atlas.Symplectic.form_nondegenerate
#print axioms Atlas.Symplectic.mem_iff_preserves
#print axioms Atlas.Symplectic.exists_isometry
#print axioms Atlas.Symplectic.exists_isometry_pair
#print axioms Atlas.Symplectic.transvection_image
#print axioms Atlas.Symplectic.transvection_conjugate
#print axioms Atlas.AlternatingForm.complement_nondegenerate
#print axioms Atlas.AlternatingForm.split_retaining_orthogonal
#print axioms Atlas.Symplectic.hyperbolicPairs_card
#print axioms Atlas.Symplectic.pairStabilizerEquiv
#print axioms Atlas.Symplectic.card_sp_succ
#print axioms Atlas.Symplectic.card_sp
#print axioms Atlas.Symplectic.mem_center_iff_scalar
#print axioms Atlas.Symplectic.centerEquivScalarKernel
#print axioms Atlas.Symplectic.card_center
#print axioms Atlas.Symplectic.card_psp_mul_center
#print axioms Atlas.Symplectic.card_psp
#print axioms Atlas.Symplectic.fixes_points_iff_central
#print axioms Atlas.Symplectic.projective_faithful
#print axioms Atlas.Symplectic.exists_generated_send
#print axioms Atlas.Symplectic.transvectionGroup_eq_top
#print axioms Atlas.Symplectic.projectiveTransvectionGroup_eq_top
#print axioms Atlas.Symplectic.perfect_of_card_gt_three
#print axioms Atlas.Symplectic.perfect_of_card_three
#print axioms Atlas.Symplectic.perfect_of_card_two
#print axioms Atlas.Symplectic.projective_perfect_of_good
#print axioms Atlas.Symplectic.projective_not_commutative
#print axioms Atlas.Symplectic.exists_isometry_orthogonal_pair
#print axioms Atlas.Symplectic.stabilizer_orbit_iff
#print axioms Atlas.Symplectic.card_perpendicular_points
#print axioms Atlas.Symplectic.card_suborbit_two_power
#print axioms Atlas.Symplectic.projective_preprimitive
#print axioms Atlas.Symplectic.iwasawa
#print axioms Atlas.Symplectic.simple_high_rank
#print axioms Atlas.Symplectic.rankOneSL
#print axioms Atlas.Symplectic.rankOnePSL
#print axioms Atlas.Symplectic.simple_of_good
#print axioms Atlas.Symplectic.rank_zero_not_simple
#print axioms Atlas.Symplectic.rank_one_two_not_simple
#print axioms Atlas.Symplectic.rank_one_three_not_simple
#print axioms Atlas.Symplectic.BinaryException.refinementEquiv
#print axioms Atlas.Symplectic.BinaryException.card_oddRefinement
#print axioms Atlas.Symplectic.BinaryException.oddRefinement_faithful
#print axioms Atlas.Symplectic.BinaryException.permutationEquiv
#print axioms Atlas.Symplectic.BinaryException.card_signKernel
#print axioms Atlas.Symplectic.exceptionalNormal_card
#print axioms Atlas.Symplectic.rank_two_two_not_simple
#print axioms Atlas.Symplectic.simple_iff_good
#print axioms Atlas.Symplectic.toPGL_injective
#print axioms Atlas.Symplectic.rankOnePSL_action
#print axioms Atlas.Symplectic.fullLinearIsometryEquiv
#print axioms Atlas.typeC_construction
#print axioms Atlas.exists_typeC
#print axioms Atlas.typeC_prime_power
#print axioms Atlas.Symplectic.Checks.galois_four
#print axioms Atlas.Symplectic.Checks.small_perfectness
#print axioms Atlas.Orthogonal.formD_apply
#print axioms Atlas.Orthogonal.formB_apply
#print axioms Atlas.Orthogonal.polarD_apply
#print axioms Atlas.Orthogonal.polarB_apply
#print axioms Atlas.Orthogonal.polarD_e
#print axioms Atlas.Orthogonal.polarD_f
#print axioms Atlas.Orthogonal.polarD_separating
#print axioms Atlas.Orthogonal.polarD_nondegenerate
#print axioms Atlas.Orthogonal.polarB_radical_iff
#print axioms Atlas.Orthogonal.formB_z
#print axioms Atlas.Orthogonal.polarB_radical_charTwo
#print axioms Atlas.Orthogonal.quadratic_radicalB_trivial
#print axioms Atlas.Orthogonal.polarB_separating_of_two_ne_zero
#print axioms Atlas.Quadratic.add_smul
#print axioms Atlas.Quadratic.polar_swap
#print axioms Atlas.Quadratic.polar_self
#print axioms Atlas.Quadratic.partner_correction
#print axioms Atlas.Quadratic.exists_normalized_partner
#print axioms Atlas.Quadratic.exists_hyperbolic_partner
#print axioms Atlas.Quadratic.partner_from_perpendicular
#print axioms Atlas.Orthogonal.exists_hyperbolic_partnerD
#print axioms Atlas.Orthogonal.exists_hyperbolic_partnerB
#print axioms Atlas.Quadratic.siegel
#print axioms Atlas.Quadratic.siegel_fix
#print axioms Atlas.Quadratic.siegel_pairing
#print axioms Atlas.Quadratic.siegel_preserves
#print axioms Atlas.Quadratic.siegel_zero
#print axioms Atlas.Quadratic.siegel_add
#print axioms Atlas.Quadratic.siegel_inverse
#print axioms Atlas.Quadratic.siegelLinear
#print axioms Atlas.Quadratic.siegelIsometry
#print axioms Atlas.Quadratic.siegel_scale
#print axioms Atlas.Quadratic.siegel_parameter_mod_line
#print axioms Atlas.Quadratic.isometry_polar
#print axioms Atlas.Quadratic.siegel_covariant
#print axioms Atlas.Quadratic.complement
#print axioms Atlas.Quadratic.mem_complement
#print axioms Atlas.Quadratic.planeProjection
#print axioms Atlas.Quadratic.planeProjection_apply
#print axioms Atlas.Quadratic.remainder_mem
#print axioms Atlas.Quadratic.split
#print axioms Atlas.Quadratic.finrank_complement
#print axioms Atlas.Quadratic.split_form
#print axioms Atlas.Quadratic.form_split
#print axioms Atlas.Quadratic.partnerEquivComplement
#print axioms Atlas.Quadratic.card_partners
#print axioms Atlas.Orthogonal.finite_orthogonal_b
#print axioms Atlas.Orthogonal.finite_orthogonal_d
#print axioms Atlas.DotProduct.functional
#print axioms Atlas.DotProduct.functional_apply
#print axioms Atlas.DotProduct.exists_normalized
#print axioms Atlas.DotProduct.card_fiber
#print axioms Atlas.DotProduct.zeroFiberEquiv
#print axioms Atlas.DotProduct.card_zeroFiber
#print axioms Atlas.Quadratic.card_nonzero_singular
#print axioms Atlas.Orthogonal.coordinatesD
#print axioms Atlas.Orthogonal.singularDFiberEquiv
#print axioms Atlas.Orthogonal.card_singularD
#print axioms Atlas.Orthogonal.BRemaining
#print axioms Atlas.Orthogonal.remainingBZeroEquiv
#print axioms Atlas.Orthogonal.remainingBEquiv
#print axioms Atlas.Orthogonal.card_remainingB
#print axioms Atlas.Orthogonal.singularBFiberEquiv
#print axioms Atlas.Orthogonal.card_singularB
#print axioms Atlas.Orthogonal.NonzeroSingularB
#print axioms Atlas.Orthogonal.NonzeroSingularD
#print axioms Atlas.Orthogonal.card_nonzero_singularB
#print axioms Atlas.Orthogonal.card_nonzero_singularD
#print axioms Atlas.Orthogonal.vectorD_finrank
#print axioms Atlas.Orthogonal.vectorB_finrank
#print axioms Atlas.Orthogonal.card_partnersB
#print axioms Atlas.Orthogonal.card_partnersD
#print axioms Atlas.Orthogonal.HyperbolicPairsB
#print axioms Atlas.Orthogonal.HyperbolicPairsD
#print axioms Atlas.Orthogonal.hyperbolicPairsBFiberEquiv
#print axioms Atlas.Orthogonal.hyperbolicPairsDFiberEquiv
#print axioms Atlas.Orthogonal.card_hyperbolicPairsB
#print axioms Atlas.Orthogonal.card_hyperbolicPairsD
#print axioms Atlas.Quadratic.reflectionFunctional
#print axioms Atlas.Quadratic.reflectionFunctional_self
#print axioms Atlas.Quadratic.reflectionLinear
#print axioms Atlas.Quadratic.reflectionLinear_apply
#print axioms Atlas.Quadratic.reflection_preserves
#print axioms Atlas.Quadratic.reflectionIsometry
#print axioms Atlas.Quadratic.sub_singular_value
#print axioms Atlas.Quadratic.reflection_transports
#print axioms Atlas.Quadratic.singular_not_polar_radical
#print axioms Atlas.Quadratic.exists_pairing_both
#print axioms Atlas.Quadratic.exists_singular_connector
#print axioms Atlas.Quadratic.exists_isometry_singular
#print axioms Atlas.Quadratic.exists_isometry_fixing_first
#print axioms Atlas.Quadratic.exists_isometry_hyperbolic_pair
#print axioms Atlas.Quadratic.complementForm
#print axioms Atlas.Quadratic.complementTransport
#print axioms Atlas.Quadratic.nonempty_complement_isometry
#print axioms Atlas.Orthogonal.radicalD_eq_bot
#print axioms Atlas.Orthogonal.radicalB_eq_bot
#print axioms Atlas.Orthogonal.singular_transitiveD
#print axioms Atlas.Orthogonal.singular_transitiveB
#print axioms Atlas.Orthogonal.pair_transitiveD
#print axioms Atlas.Orthogonal.pair_transitiveB
#print axioms Atlas.Orthogonal.insertD
#print axioms Atlas.Orthogonal.tailD
#print axioms Atlas.Orthogonal.tail_insertD
#print axioms Atlas.Orthogonal.form_insertD
#print axioms Atlas.Orthogonal.standardComplementD
#print axioms Atlas.Orthogonal.polarB_e0
#print axioms Atlas.Orthogonal.polarB_f0
#print axioms Atlas.Orthogonal.standardComplementB
#print axioms Atlas.Orthogonal.formD_e
#print axioms Atlas.Orthogonal.formD_f
#print axioms Atlas.Orthogonal.polarD_ef
#print axioms Atlas.Orthogonal.complement_isometryD
#print axioms Atlas.Orthogonal.complement_isometryB
#print axioms Atlas.Quadratic.complementExtensionLinear
#print axioms Atlas.Quadratic.complementExtension_preserves
#print axioms Atlas.Quadratic.complementExtension
#print axioms Atlas.Quadratic.split_e
#print axioms Atlas.Quadratic.split_f
#print axioms Atlas.Quadratic.split_complement
#print axioms Atlas.Quadratic.complementExtension_fix_e
#print axioms Atlas.Quadratic.complementExtension_fix_f
#print axioms Atlas.Quadratic.complementExtension_apply
#print axioms Atlas.Quadratic.scalarIsometry
#print axioms Atlas.Quadratic.squareOneEquivSigns
#print axioms Atlas.Quadratic.card_squareOne
#print axioms Atlas.Orthogonal.pairStabilizer
#print axioms Atlas.Orthogonal.pairRestriction
#print axioms Atlas.Orthogonal.pairRestriction_injective
#print axioms Atlas.Orthogonal.pairRestriction_surjective
#print axioms Atlas.Orthogonal.pairStabilizerEquiv
#print axioms Atlas.Orthogonal.isometryGroupTransport
#print axioms Atlas.Orthogonal.hyperbolicPairs
#print axioms Atlas.Orthogonal.hyperbolicPairsAction
#print axioms Atlas.Orthogonal.hyperbolicPairs_pretransitive
#print axioms Atlas.Orthogonal.hyperbolicPairs_stabilizer
#print axioms Atlas.Orthogonal.card_isometry_eq_pairs_mul_complement
#print axioms Atlas.Orthogonal.standardPairD
#print axioms Atlas.Orthogonal.standardPairB
#print axioms Atlas.Orthogonal.standardPairStabilizerD
#print axioms Atlas.Orthogonal.standardPairStabilizerB
#print axioms Atlas.Orthogonal.card_fullB_succ
#print axioms Atlas.Orthogonal.card_fullD_succ
#print axioms Atlas.Orthogonal.rankZero_vectorB
#print axioms Atlas.Orthogonal.formB_zeroRank
#print axioms Atlas.Orthogonal.rankZeroBEquiv
#print axioms Atlas.Orthogonal.card_fullB_zero
#print axioms Atlas.Orthogonal.card_fullD_zero
#print axioms Atlas.Orthogonal.card_fullB
#print axioms Atlas.Orthogonal.difference_square
#print axioms Atlas.Orthogonal.card_fullD
#print axioms Atlas.Quadratic.squareRootLinear
#print axioms Atlas.Quadratic.squareRootLinear_sq
#print axioms Atlas.Orthogonal.polarD_eq_symplectic
#print axioms Atlas.Orthogonal.even_fix_z
#print axioms Atlas.Orthogonal.even_first
#print axioms Atlas.Orthogonal.evenProjectionLinear
#print axioms Atlas.Orthogonal.evenProjection_preserves
#print axioms Atlas.Orthogonal.evenProjection
#print axioms Atlas.Orthogonal.evenDefect
#print axioms Atlas.Orthogonal.evenDefect_polar
#print axioms Atlas.Orthogonal.evenCorrection
#print axioms Atlas.Orthogonal.evenCorrection_sq
#print axioms Atlas.Orthogonal.evenLiftLinear
#print axioms Atlas.Orthogonal.evenLift_preserves
#print axioms Atlas.Orthogonal.evenLift
#print axioms Atlas.Orthogonal.evenProjection_apply
#print axioms Atlas.Orthogonal.evenProjection_injective
#print axioms Atlas.Orthogonal.evenProjection_lift
#print axioms Atlas.Orthogonal.evenProjection_surjective
#print axioms Atlas.Orthogonal.evenFullEquivSp
#print axioms Atlas.Orthogonal.even_symplectic_center
#print axioms Atlas.Orthogonal.evenFullEquivPSp
#print axioms Atlas.Orthogonal.even_full_simple_iff
#print axioms Atlas.Orthogonal.even_full_perfect
#print axioms Atlas.Orthogonal.even_full_noncommutative
#print axioms Atlas.Orthogonal.siegelElement
#print axioms Atlas.Orthogonal.elementarySubgroup
#print axioms Atlas.Orthogonal.siegelElement_mem
#print axioms Atlas.Orthogonal.evenSingularLift
#print axioms Atlas.Orthogonal.evenSingularLift_singular
#print axioms Atlas.Orthogonal.polarB_scalar_z
#print axioms Atlas.Orthogonal.even_siegel_transvection
#print axioms Atlas.Orthogonal.even_transvection_mem_image
#print axioms Atlas.Orthogonal.even_elementary_eq_top
#print axioms Atlas.Orthogonal.semilinearIsometryGroupTransport
#print axioms Atlas.Orthogonal.fieldCoordinatesD
#print axioms Atlas.Orthogonal.fieldCoordinatesB
#print axioms Atlas.Orthogonal.fieldCoordinatesD_form
#print axioms Atlas.Orthogonal.fieldCoordinatesB_form
#print axioms Atlas.Orthogonal.fieldEquivFullD
#print axioms Atlas.Orthogonal.fieldEquivFullB
#print axioms Atlas.Orthogonal.matrixLinearEquiv
#print axioms Atlas.Orthogonal.matrixIsometrySubgroup
#print axioms Atlas.Orthogonal.mem_matrixIsometry
#print axioms Atlas.Orthogonal.matrixIsometryEquiv
#print axioms Atlas.Orthogonal.matrixLinearEquiv_coordinates
#print axioms Atlas.Quadratic.siegel_transvection_factorization
#print axioms Atlas.Quadratic.siegelLinear_det
#print axioms Atlas.Quadratic.siegelIsometry_det
#print axioms Atlas.Quadratic.isometry_det_sq
#print axioms Atlas.Quadratic.reflection_det
#print axioms Atlas.squareOneUnitsEquiv
#print axioms Atlas.card_squareOneUnits
#print axioms Atlas.Orthogonal.determinant
#print axioms Atlas.Orthogonal.specialSubgroup
#print axioms Atlas.Orthogonal.mem_specialSubgroup
#print axioms Atlas.Orthogonal.siegelElement_determinant
#print axioms Atlas.Orthogonal.elementary_le_special
#print axioms Atlas.Orthogonal.determinantSign
#print axioms Atlas.Orthogonal.determinantSign_kernel
#print axioms Atlas.Orthogonal.reflectionElement
#print axioms Atlas.Orthogonal.reflectionElement_determinant
#print axioms Atlas.Orthogonal.determinantSign_surjective
#print axioms Atlas.Orthogonal.card_special_mul_sign
#print axioms Atlas.Orthogonal.SO_B
#print axioms Atlas.Orthogonal.SO_DPlus
#print axioms Atlas.Orthogonal.polarB_nondegenerate
#print axioms Atlas.Orthogonal.formD_anisotropic
#print axioms Atlas.Orthogonal.card_specialB_mul_two
#print axioms Atlas.Orthogonal.card_specialD_mul_sign
#print axioms Atlas.Orthogonal.even_specialD_eq_top
#print axioms Atlas.Orthogonal.even_specialB_eq_top
#print axioms Atlas.Orthogonal.card_specialB
#print axioms Atlas.Orthogonal.card_specialD
#print axioms Atlas.Quadratic.residualMap
#print axioms Atlas.Quadratic.residual
#print axioms Atlas.Quadratic.residualMap_apply
#print axioms Atlas.Quadratic.residualSection
#print axioms Atlas.Quadratic.residualSection_spec
#print axioms Atlas.Quadratic.fixed_perpendicular_residual
#print axioms Atlas.Quadratic.wallForm
#print axioms Atlas.Quadratic.wallForm_residual
#print axioms Atlas.Quadratic.wallForm_self
#print axioms Atlas.Quadratic.wallForm_symmetrization
#print axioms Atlas.Quadratic.wallForm_unique
#print axioms Atlas.Quadratic.fixed_iff_perpendicular_residual
#print axioms Atlas.Quadratic.wallForm_nondegenerate
#print axioms Atlas.squareUnits
#print axioms Atlas.SquareClass
#print axioms Atlas.squareClass
#print axioms Atlas.squareClass_eq_one
#print axioms Atlas.squareClass_square
#print axioms Atlas.squareClass_mul_square
#print axioms Atlas.squareClass_surjective
#print axioms Atlas.card_squareClass
#print axioms Atlas.Bilinear.gramUnit
#print axioms Atlas.Bilinear.determinantClass
#print axioms Atlas.Bilinear.gramUnit_basis_change
#print axioms Atlas.Bilinear.determinantClass_basis_independent
#print axioms Atlas.Quadratic.wallDeterminantClass
#print axioms Atlas.Quadratic.wallDeterminantClass_basis
#print axioms Atlas.Quadratic.sub_value
#print axioms Atlas.Quadratic.reflection_equal_value
#print axioms Atlas.Quadratic.reflection_self
#print axioms Atlas.Quadratic.equal_value_transport
#print axioms Atlas.Quadratic.linePerp
#print axioms Atlas.Quadratic.lineCoordinate
#print axioms Atlas.Quadratic.lineCoordinate_self
#print axioms Atlas.Quadratic.lineCoordinate_perp
#print axioms Atlas.Quadratic.lineRemainder_mem
#print axioms Atlas.Quadratic.lineSplit
#print axioms Atlas.Quadratic.linePerp_finrank
#print axioms Atlas.Quadratic.linePerpForm
#print axioms Atlas.Quadratic.linePerpForm_polar
#print axioms Atlas.Quadratic.lineSplit_form
#print axioms Atlas.Quadratic.linePerpForm_nondegenerate
#print axioms Atlas.Quadratic.lineExtensionLinear
#print axioms Atlas.Quadratic.lineExtension_preserves
#print axioms Atlas.Quadratic.lineExtension
#print axioms Atlas.Quadratic.lineSplit_self
#print axioms Atlas.Quadratic.lineSplit_perp
#print axioms Atlas.Quadratic.lineExtension_fix
#print axioms Atlas.Quadratic.lineExtension_apply
#print axioms Atlas.Quadratic.linear_ext_linePerp
#print axioms Atlas.Quadratic.lineRestriction
#print axioms Atlas.Quadratic.lineExtension_restriction
#print axioms Atlas.Quadratic.lineExtension_reflection
#print axioms Atlas.Orthogonal.reflectionSubgroup
#print axioms Atlas.Orthogonal.reflectionElement_mem
#print axioms Atlas.Orthogonal.reflectionSubgroup_transport
#print axioms Atlas.Orthogonal.lineExtensionHom
#print axioms Atlas.Orthogonal.lineExtensionHom_reflection
#print axioms Atlas.Orthogonal.lineExtensionHom_mem
#print axioms Atlas.Orthogonal.reflection_generation_dim
#print axioms Atlas.Orthogonal.reflectionSubgroup_eq_top
#print axioms Atlas.Quadratic.wallForm_residual_right
#print axioms Atlas.Quadratic.reflectedIsometry
#print axioms Atlas.Quadratic.reflected_residual
#print axioms Atlas.Quadratic.wallComplement
#print axioms Atlas.Quadratic.wallProjection
#print axioms Atlas.Quadratic.wallProjection_apply
#print axioms Atlas.Quadratic.wallProjection_mem
#print axioms Atlas.Quadratic.wallProjection_fixed
#print axioms Atlas.Quadratic.reflected_residual_projection
#print axioms Atlas.Quadratic.reflected_residual_eq
#print axioms Atlas.Quadratic.reflectedResidualInclusion
#print axioms Atlas.Quadratic.reflectedResidualInclusion_perp
#print axioms Atlas.Quadratic.reflectedResidualInclusion_map
#print axioms Atlas.Quadratic.reflected_wallForm
#print axioms Atlas.Quadratic.reflectedResidualEquiv
#print axioms Atlas.Quadratic.reflected_residual_finrank
#print axioms Atlas.Bilinear.linePerp
#print axioms Atlas.Bilinear.lineCoordinate
#print axioms Atlas.Bilinear.lineCoordinate_self
#print axioms Atlas.Bilinear.lineCoordinate_perp
#print axioms Atlas.Bilinear.lineRemainder_mem
#print axioms Atlas.Bilinear.lineSplit
#print axioms Atlas.Bilinear.linePerp_finrank
#print axioms Atlas.Bilinear.linePerpForm
#print axioms Atlas.Bilinear.lineBasis
#print axioms Atlas.Bilinear.lineBasis_inl
#print axioms Atlas.Bilinear.lineBasis_inr
#print axioms Atlas.Bilinear.lineBasis_det
#print axioms Atlas.Bilinear.linePerpForm_nondegenerate
#print axioms Atlas.Bilinear.determinantClass_reindex
#print axioms Atlas.Bilinear.determinantClass_basis_independent_any
#print axioms Atlas.Bilinear.determinantClass_transport
#print axioms Atlas.Bilinear.determinantClass_line
#print axioms Atlas.Quadratic.wallDeterminantClass_reflection_residual
#print axioms Atlas.Quadratic.fixed_iff_mem_residual_orthogonal
#print axioms Atlas.Quadratic.outside_residual_fixed_witness
#print axioms Atlas.Quadratic.outside_mem_reflected_residual
#print axioms Atlas.Quadratic.reflectedIsometry_twice
#print axioms Atlas.Quadratic.wallDeterminantClass_reflection
#print axioms Atlas.Orthogonal.wallClass
#print axioms Atlas.Orthogonal.wallClass_one
#print axioms Atlas.Orthogonal.wallClass_reflection_mul
#print axioms Atlas.Orthogonal.wallClass_reflection
#print axioms Atlas.Orthogonal.wallClass_mul
#print axioms Atlas.Orthogonal.spinorNorm
#print axioms Atlas.Orthogonal.spinorNorm_reflection
#print axioms Atlas.Orthogonal.specialSpinorNorm
#print axioms Atlas.Orthogonal.specialSpinorKernel
#print axioms Atlas.Orthogonal.specialSpinorKernel_normal
#print axioms Atlas.Orthogonal.specialSpinorNorm_surjective
#print axioms Atlas.Orthogonal.specialSpinorQuotientEquiv
#print axioms Atlas.Orthogonal.card_specialSpinorKernel_mul_two
#print axioms Atlas.Orthogonal.formD_represents
#print axioms Atlas.Orthogonal.formB_represents
#print axioms Atlas.Orthogonal.oddSpinorKernelB
#print axioms Atlas.Orthogonal.oddSpinorKernelD
#print axioms Atlas.Orthogonal.card_oddSpinorKernelB
#print axioms Atlas.Orthogonal.card_oddSpinorKernelD
#print axioms Atlas.Orthogonal.siegel_reflection_vector_value
#print axioms Atlas.Orthogonal.siegelElement_reflection_factor
#print axioms Atlas.Orthogonal.siegelElement_add
#print axioms Atlas.Orthogonal.spinorNorm_siegel
#print axioms Atlas.Orthogonal.elementary_le_spinorKernel
#print axioms Atlas.Orthogonal.commutator_le_spinorKernel
#print axioms Atlas.Orthogonal.elementary_le_special_spinor
#print axioms Atlas.Orthogonal.commutator_le_special_spinor
#print axioms Atlas.Orthogonal.siegelElement_conj
#print axioms Atlas.Orthogonal.elementarySubgroup_normal
#print axioms Atlas.Orthogonal.rootParameterSpace
#print axioms Atlas.Orthogonal.rootParameterHom
#print axioms Atlas.Orthogonal.rootSubgroup
#print axioms Atlas.Orthogonal.rootSubgroup_le_elementary
#print axioms Atlas.Orthogonal.rootSubgroup_isMulCommutative
#print axioms Atlas.Orthogonal.rootParameterQuotientEquiv
#print axioms Atlas.Orthogonal.rootParameter_kernel
#print axioms Atlas.Orthogonal.rootComplementHom
#print axioms Atlas.Orthogonal.rootComplementHom_injective
#print axioms Atlas.Orthogonal.rootPerpendicularRepresentative
#print axioms Atlas.Orthogonal.rootPerpendicularRepresentative_element
#print axioms Atlas.Orthogonal.rootComplementHom_range
#print axioms Atlas.Orthogonal.rootComplementEquiv
#print axioms Atlas.Orthogonal.card_rootSubgroup
#print axioms Atlas.Orthogonal.rootSubgroup_scale_le
#print axioms Atlas.Orthogonal.rootSubgroup_scale
#print axioms Atlas.Orthogonal.rootSubgroup_conj
#print axioms Atlas.Orthogonal.line_stabilizer_normalizes_root
#print axioms Atlas.Quadratic.complement_singular_decomposition
#print axioms Atlas.Quadratic.linear_zero_of_singular
#print axioms Atlas.Quadratic.exists_singular_functional_ne_zero
#print axioms Atlas.Quadratic.transportParameter
#print axioms Atlas.Quadratic.transportParameter_perp
#print axioms Atlas.Quadratic.difference_polar_value
#print axioms Atlas.Quadratic.siegel_equal_value_transport
#print axioms Atlas.Quadratic.isotropic_plane_perpendicular
#print axioms Atlas.Quadratic.perpendicular_hyperbolic_partner
#print axioms Atlas.Quadratic.WittTwoFrame
#print axioms Atlas.Quadratic.WittTwoFrame.first_ne_zero
#print axioms Atlas.Quadratic.WittTwoFrame.second_not_multiple
#print axioms Atlas.Quadratic.hyperbolic_pair_in_perpendicular
#print axioms Atlas.Quadratic.polar_restriction_ne_zero
#print axioms Atlas.Quadratic.exists_singular_perpendicular_witness
#print axioms Atlas.Orthogonal.elementary_transport_with_direction
#print axioms Atlas.Orthogonal.nonsingular_not_span_difference
#print axioms Atlas.Orthogonal.elementary_transport_not_opposite
#print axioms Atlas.Orthogonal.elementary_transport_equal_value
#print axioms Atlas.Orthogonal.wittTwoFrameD
#print axioms Atlas.Orthogonal.wittTwoFrameB
#print axioms Atlas.Orthogonal.elementary_transportB
#print axioms Atlas.Orthogonal.elementary_transportD
#print axioms Atlas.card_le_four_of_two_commuting_involutions
#print axioms Atlas.Orthogonal.reflectionElement_conj
#print axioms Atlas.Orthogonal.reflectionElement_inv
#print axioms Atlas.Orthogonal.reflectionElement_square
#print axioms Atlas.Orthogonal.reflectionElement_smul
#print axioms Atlas.Orthogonal.ElementaryQuotient
#print axioms Atlas.Orthogonal.elementaryProjection
#print axioms Atlas.Orthogonal.elementaryProjection_reflection_equal_value
#print axioms Atlas.Orthogonal.elementaryProjection_reflection_central
#print axioms Atlas.Orthogonal.elementaryQuotient_isMulCommutative
#print axioms Atlas.Orthogonal.commutator_le_elementary
#print axioms Atlas.Orthogonal.equal_norm_reflection_product_mem_commutator
#print axioms Atlas.Orthogonal.anisotropic_siegel_mem_commutator
#print axioms Atlas.Orthogonal.isotropic_parameter_anisotropic_sum
#print axioms Atlas.Orthogonal.siegel_mem_commutator
#print axioms Atlas.Orthogonal.elementary_eq_commutator
#print axioms Atlas.Orthogonal.elementaryProjection_reflection_squareClass
#print axioms Atlas.Orthogonal.frame_represents
#print axioms Atlas.Orthogonal.card_elementaryQuotient_le_four
#print axioms Atlas.Orthogonal.determinantSpinor
#print axioms Atlas.Orthogonal.determinantSpinor_kernel
#print axioms Atlas.Orthogonal.determinantSpinor_surjective
#print axioms Atlas.Orthogonal.determinantSpinor_kernel_index
#print axioms Atlas.Orthogonal.elementary_eq_intrinsicKernel
#print axioms Atlas.Orthogonal.elementarySpecialSpinorEquiv
#print axioms Atlas.Orthogonal.elementaryB_eq_intrinsicKernel
#print axioms Atlas.Orthogonal.elementaryD_eq_intrinsicKernel
#print axioms Atlas.Orthogonal.elementaryB_eq_commutator
#print axioms Atlas.Orthogonal.elementaryD_eq_commutator
#print axioms Atlas.Orthogonal.elementaryB_kernelEquiv
#print axioms Atlas.Orthogonal.elementaryD_kernelEquiv
#print axioms Atlas.Orthogonal.card_elementaryB
#print axioms Atlas.Orthogonal.card_elementaryD
#print axioms Atlas.Orthogonal.hyperbolic_reflection_norm
#print axioms Atlas.Orthogonal.hyperbolicReflection
#print axioms Atlas.Orthogonal.hyperbolicReflection_e
#print axioms Atlas.Orthogonal.hyperbolicReflection_f
#print axioms Atlas.Orthogonal.hyperbolicReflection_perp
#print axioms Atlas.Orthogonal.hyperbolicTorus
#print axioms Atlas.Orthogonal.hyperbolicTorus_e
#print axioms Atlas.Orthogonal.hyperbolicTorus_f
#print axioms Atlas.Orthogonal.hyperbolicTorus_perp
#print axioms Atlas.Orthogonal.squareTorus_mem_elementary
#print axioms Atlas.Orthogonal.torus_root_conj
#print axioms Atlas.Orthogonal.root_mem_elementary_commutator_of_scalar
#print axioms Atlas.Orthogonal.siegel_mem_elementary_commutator
#print axioms Atlas.Orthogonal.elementary_perfect_of_card_gt_three
#print axioms Atlas.Orthogonal.elementaryB_perfect_of_card_gt_three
#print axioms Atlas.Orthogonal.elementaryD_perfect_of_card_gt_three
#print axioms Atlas.Orthogonal.oddSpinorKernelB_perfect_of_card_gt_three
#print axioms Atlas.Orthogonal.oddSpinorKernelD_perfect_of_card_gt_three
#print axioms Atlas.Orthogonal.siegel_mem_commutator_of_scaling
#print axioms Atlas.Orthogonal.hyperbolicTorus_determinant
#print axioms Atlas.Orthogonal.hyperbolicTorus_spinorNorm
#print axioms Atlas.Orthogonal.compensatedTorus
#print axioms Atlas.Orthogonal.compensatedTorus_mem_elementary
#print axioms Atlas.Orthogonal.compensatedTorus_e
#print axioms Atlas.Orthogonal.compensatedTorus_perp
#print axioms Atlas.Quadratic.isometry_between_polar
#print axioms Atlas.Quadratic.complementForm_polar
#print axioms Atlas.Quadratic.complement_perpendicular_pair
#print axioms Atlas.Orthogonal.root_mem_commutator_of_complement
#print axioms Atlas.Orthogonal.elementary_perfect_of_standard_complements
#print axioms Atlas.Orthogonal.elementaryB_perfect_stable
#print axioms Atlas.Orthogonal.elementaryD_perfect_stable
#print axioms Atlas.Orthogonal.oddSpinorKernelB_perfect_stable
#print axioms Atlas.Orthogonal.oddSpinorKernelD_perfect_stable
#print axioms Atlas.Orthogonal.pairStabilizer_projection_surjective
#print axioms Atlas.Orthogonal.elementary_transport_hyperbolic_pair
#print axioms Atlas.Orthogonal.complementB_represents
#print axioms Atlas.Orthogonal.complementD_represents
#print axioms Atlas.Orthogonal.elementaryB_pair_transport
#print axioms Atlas.Orthogonal.elementaryD_pair_transport
#print axioms Atlas.Orthogonal.elementaryB_singular_transport
#print axioms Atlas.Orthogonal.elementaryD_singular_transport
#print axioms Atlas.Orthogonal.elementary_nontrivial_of_pair_transport
#print axioms Atlas.Orthogonal.elementaryB_nontrivial
#print axioms Atlas.Orthogonal.elementaryD_nontrivial
#print axioms Atlas.Orthogonal.elementaryB_noncommutative_stable
#print axioms Atlas.Orthogonal.elementaryD_noncommutative_stable
#print axioms Atlas.Orthogonal.elementaryB_noncommutative_of_card_gt_three
#print axioms Atlas.Orthogonal.elementaryD_noncommutative_of_card_gt_three
#print axioms Atlas.Orthogonal.oddSpinorKernelB_noncommutative_stable
#print axioms Atlas.Orthogonal.oddSpinorKernelD_noncommutative_stable
#print axioms Atlas.Orthogonal.rootComplement_partner
#print axioms Atlas.Orthogonal.rootPartnerEquiv
#print axioms Atlas.Orthogonal.rootPartnerEquiv_apply
#print axioms Atlas.Orthogonal.root_unique_partner_transport
#print axioms Atlas.Orthogonal.rootSubgroup_fixes_direction
#print axioms Atlas.Orthogonal.root_fixed_iff
#print axioms Atlas.Orthogonal.root_centralizer_preserves_line
#print axioms Atlas.Orthogonal.centralizer_siegel_commutes
#print axioms Atlas.Orthogonal.centralizer_isotropic_parameter
#print axioms Atlas.Orthogonal.elementary_centralizer_scalar
#print axioms Atlas.Orthogonal.elementary_centralizer_scalar_of_frame
#print axioms Atlas.Orthogonal.mem_elementary_center_iff_scalar
#print axioms Atlas.Orthogonal.elementary_noncommutative_of_frame
#print axioms Atlas.Orthogonal.elementaryB_noncommutative
#print axioms Atlas.Orthogonal.elementaryD_noncommutative
#print axioms Atlas.Orthogonal.elementaryD_center_scalar
#print axioms Atlas.Orthogonal.elementaryB_center_eq_bot
#print axioms Atlas.Orthogonal.elementaryD_center_eq_bot_of_two_eq_zero
#print axioms Atlas.Orthogonal.elementaryScalarSubgroup
#print axioms Atlas.Orthogonal.elementaryScalarSubgroup_le_center
#print axioms Atlas.Orthogonal.elementaryScalarSubgroup_normal
#print axioms Atlas.Orthogonal.elementaryScalarSubgroup_eq_center
#print axioms Atlas.Orthogonal.ProjectiveElementary
#print axioms Atlas.Orthogonal.projectiveElementaryGroup
#print axioms Atlas.Orthogonal.projectiveElementaryFinite
#print axioms Atlas.Orthogonal.projectiveElementaryMap
#print axioms Atlas.Orthogonal.projectiveElementaryMap_surjective
#print axioms Atlas.Orthogonal.projectiveElementaryMap_kernel
#print axioms Atlas.Orthogonal.projectiveElementaryCenterEquiv
#print axioms Atlas.Orthogonal.projectiveElementary_perfect
#print axioms Atlas.Orthogonal.projectiveElementaryBEquiv
#print axioms Atlas.Orthogonal.projectiveElementaryB_noncommutative
#print axioms Atlas.Orthogonal.projectiveBKernelEquiv
#print axioms Atlas.Orthogonal.card_projectiveElementaryB
#print axioms Atlas.Orthogonal.card_projectiveElementaryB_mul_two
#print axioms Atlas.Orthogonal.projectiveElementaryB_perfect_stable
#print axioms Atlas.Orthogonal.projectiveElementaryB_perfect_of_card_gt_three
#print axioms Atlas.units_square_iff_field_square
#print axioms Atlas.odd_power_mod_four
#print axioms Atlas.sign_power_square_iff_card_pow_mod_four
#print axioms Atlas.odd_card_mod_two
#print axioms Atlas.twice_sign_center_factor
#print axioms Atlas.Orthogonal.signTorusD
#print axioms Atlas.Orthogonal.signTorusD_e
#print axioms Atlas.Orthogonal.signTorusD_f
#print axioms Atlas.Orthogonal.signProductD
#print axioms Atlas.Orthogonal.signProductD_e
#print axioms Atlas.Orthogonal.signProductD_f
#print axioms Atlas.Orthogonal.negativeScalarD
#print axioms Atlas.Orthogonal.negativeScalarD_eq_signProduct
#print axioms Atlas.Orthogonal.signProductD_spinorNorm
#print axioms Atlas.Orthogonal.negativeScalarD_spinorNorm
#print axioms Atlas.Orthogonal.signProductD_determinant
#print axioms Atlas.Orthogonal.negativeScalarD_determinant
#print axioms Atlas.Orthogonal.elementaryD_center_signs
#print axioms Atlas.Orthogonal.negativeScalarD_ne_one
#print axioms Atlas.Orthogonal.negativeScalarD_mem_elementary_iff
#print axioms Atlas.Orthogonal.card_elementaryD_center
#print axioms Atlas.Orthogonal.negativeScalarD_mem_elementary_iff_mod_four
#print axioms Atlas.Orthogonal.card_elementaryD_center_mod_four
#print axioms Atlas.Orthogonal.card_elementaryD_center_mul_two
#print axioms Atlas.Orthogonal.card_elementaryD_mul_two
#print axioms Atlas.Orthogonal.card_projectiveElementaryD_mul_gcd
#print axioms Atlas.Orthogonal.card_projectiveElementaryD
#print axioms Atlas.Orthogonal.projectiveElementaryD_order_divisibility
#print axioms Atlas.Orthogonal.projectiveElementaryD_perfect_stable
#print axioms Atlas.Orthogonal.projectiveElementaryD_nontrivial
#print axioms Atlas.Orthogonal.projectiveElementaryD_noncommutative_stable
#print axioms Atlas.Orthogonal.semilinear_polar_transport
#print axioms Atlas.Orthogonal.semilinear_siegel_covariant
#print axioms Atlas.Orthogonal.semilinear_siegelElement
#print axioms Atlas.Orthogonal.semilinear_elementary_map
#print axioms Atlas.Orthogonal.semilinearElementaryEquiv
#print axioms Atlas.Orthogonal.fieldEquivElementaryB
#print axioms Atlas.Orthogonal.fieldEquivElementaryD
#print axioms Atlas.Orthogonal.semilinearElementaryEquiv_apply
#print axioms Atlas.Orthogonal.semilinear_scalar_membership
#print axioms Atlas.Orthogonal.semilinear_scalar_map
#print axioms Atlas.Orthogonal.semilinearProjectiveElementaryEquiv
#print axioms Atlas.Orthogonal.semilinearProjectiveElementaryEquiv_mk
#print axioms Atlas.Orthogonal.fieldEquivProjectiveElementaryB
#print axioms Atlas.Orthogonal.fieldEquivProjectiveElementaryD
#print axioms Atlas.Orthogonal.fieldEquivOddKernelB
#print axioms Atlas.Orthogonal.fieldEquivOddKernelD
#print axioms Atlas.Orthogonal.fieldEquivOddKernelB_full
#print axioms Atlas.Orthogonal.fieldEquivOddKernelD_full
#print axioms Atlas.GroupTheory.block_contains_stabilizer_transport
#print axioms Atlas.GroupTheory.primitive_of_two_suborbits_and_connectors
#print axioms Atlas.Quadratic.isometry_between_nondegenerate
#print axioms Atlas.Quadratic.isometry_between_nondegenerate_iff
#print axioms Atlas.Orthogonal.complementLift
#print axioms Atlas.Orthogonal.complementLift_fix_e
#print axioms Atlas.Orthogonal.complementLift_fix_f
#print axioms Atlas.Orthogonal.complementLift_apply
#print axioms Atlas.Orthogonal.complementLift_injective
#print axioms Atlas.Orthogonal.complementLift_siegel
#print axioms Atlas.Orthogonal.complementLift_maps_elementary
#print axioms Atlas.Orthogonal.complementLift_mem_elementary
#print axioms Atlas.Orthogonal.complementElementaryLift
#print axioms Atlas.Orthogonal.complementElementaryLift_injective
#print axioms Atlas.Orthogonal.complement_polar_surjective
#print axioms Atlas.Orthogonal.root_transport_perpendicular_coordinate
#print axioms Atlas.Orthogonal.elementary_transport_perpendicular_coordinate
#print axioms Atlas.Orthogonal.perpendicular_singular_decomposition
#print axioms Atlas.Orthogonal.elementary_perpendicular_stabilizer_transport
#print axioms Atlas.Orthogonal.elementary_singular_transport_of_isometry
#print axioms Atlas.Orthogonal.elementaryB_perpendicular_stabilizer_transport
#print axioms Atlas.Orthogonal.singular_line_scalars_equal
#print axioms Atlas.Orthogonal.singular_line_kernel_scalar
#print axioms Atlas.Orthogonal.singular_projective_kernel_scalar
#print axioms Atlas.Orthogonal.singular_mk_iff
#print axioms Atlas.Orthogonal.SingularPoints
#print axioms Atlas.Orthogonal.singularPointMk
#print axioms Atlas.Orthogonal.singularPointMk_rep
#print axioms Atlas.Orthogonal.singularPointMk_smul
#print axioms Atlas.Orthogonal.singularPoints_pretransitive
#print axioms Atlas.Orthogonal.singularPointsB_pretransitive
#print axioms Atlas.Orthogonal.scalar_fixes_singularPoints
#print axioms Atlas.Orthogonal.fixes_singularPoints_iff_scalar
#print axioms Atlas.Orthogonal.singularPointPerm
#print axioms Atlas.Orthogonal.singularPointPerm_kernel
#print axioms Atlas.Orthogonal.projectiveSingularPerm
#print axioms Atlas.Orthogonal.projectiveSingular_projection_smul
#print axioms Atlas.Orthogonal.projectiveSingular_faithful
#print axioms Atlas.Orthogonal.projectiveSingular_pretransitive
#print axioms Atlas.Orthogonal.projectiveSingularB_faithful
#print axioms Atlas.Orthogonal.projectiveSingularB_pretransitive
#print axioms Atlas.Orthogonal.root_normalClosure_eq_top
#print axioms Atlas.Orthogonal.rootB_normalClosure_eq_top
#print axioms Atlas.Orthogonal.SingularPerp
#print axioms Atlas.Orthogonal.singularPerp_symmetric
#print axioms Atlas.Orthogonal.singularPerp_self
#print axioms Atlas.Orthogonal.singularPerp_mk_iff
#print axioms Atlas.Orthogonal.singularPerp_smul_iff
#print axioms Atlas.Orthogonal.singular_normalized_partner
#print axioms Atlas.Orthogonal.root_nonperpendicular_transport
#print axioms Atlas.Orthogonal.singular_stabilizer_nonperpendicular_transitive
#print axioms Atlas.Orthogonal.not_mem_span_difference_of_independent
#print axioms Atlas.Orthogonal.exists_singular_nonperpendicular_connector
#print axioms Atlas.Orthogonal.perpendicular_not_mem_span
#print axioms Atlas.Orthogonal.exists_singular_perpendicular_connectorB
#print axioms Atlas.Orthogonal.singularPoints_rep_not_mem_span
#print axioms Atlas.Orthogonal.singularPoints_smul_eq_of_rep
#print axioms Atlas.Orthogonal.singular_stabilizerB_perpendicular_transitive
#print axioms Atlas.Orthogonal.singularPointMk_ne_of_not_mem_span
#print axioms Atlas.Orthogonal.singularPointsB_perpendicular_connector
#print axioms Atlas.Orthogonal.singularPointsB_nonperpendicular_connector
#print axioms Atlas.Orthogonal.singularPointsB_faithful
#print axioms Atlas.Orthogonal.singularPointsB_primitive
#print axioms Atlas.Orthogonal.elementaryRoot_le_point_stabilizer
#print axioms Atlas.Orthogonal.elementaryRoot_normal_point_stabilizer
#print axioms Atlas.Orthogonal.elementaryB_simple_stable
#print axioms Atlas.Orthogonal.projectiveElementaryB_simple_stable
#print axioms Atlas.Orthogonal.oddSpinorKernelB_simple_stable
#print axioms Atlas.Orthogonal.even_elementaryScalar_eq_bot
#print axioms Atlas.Orthogonal.evenProjectiveElementaryEquiv
#print axioms Atlas.Orthogonal.evenElementaryBEquivFull
#print axioms Atlas.Orthogonal.evenProjectiveBEquivFull
#print axioms Atlas.Orthogonal.evenProjectiveBEquivPSp
#print axioms Atlas.Orthogonal.evenProjectiveBEquivFull_projection
#print axioms Atlas.Orthogonal.card_evenProjectiveB
#print axioms Atlas.Orthogonal.even_projectiveB_simple_iff
#print axioms Atlas.Orthogonal.even_projectiveB_simple_iff_rank_ge_two
#print axioms Atlas.Orthogonal.even_projectiveB_simple_stable
#print axioms Atlas.Orthogonal.even_projectiveB_perfect
#print axioms Atlas.Orthogonal.even_projectiveB_noncommutative
#print axioms Atlas.Orthogonal.card_projectiveB_all_char
#print axioms Atlas.Orthogonal.projectiveB_simple_all_char
#print axioms Atlas.Orthogonal.projectiveB_noncommutative_all_char
#print axioms Atlas.Quadratic.dicksonParity
#print axioms Atlas.Quadratic.dickson_reflectedIsometry_twice
#print axioms Atlas.Quadratic.reflected_residual_finrank_outside
#print axioms Atlas.Quadratic.dicksonParity_reflection
#print axioms Atlas.Orthogonal.dicksonParity_mul_of_mem_reflectionSubgroup
#print axioms Atlas.Orthogonal.reflectionDicksonCharacter
#print axioms Atlas.Orthogonal.dicksonValue
#print axioms Atlas.Orthogonal.dicksonValue_one
#print axioms Atlas.Orthogonal.residual_inverse
#print axioms Atlas.Orthogonal.dicksonValue_inv
#print axioms Atlas.Orthogonal.residual_isometry_transport
#print axioms Atlas.Orthogonal.dicksonValue_isometry_transport
#print axioms Atlas.Orthogonal.exchange_direction_value
#print axioms Atlas.Orthogonal.exchange_direction_nonzero
#print axioms Atlas.Orthogonal.hyperbolicExchange
#print axioms Atlas.Orthogonal.hyperbolicExchange_e
#print axioms Atlas.Orthogonal.hyperbolicExchange_f
#print axioms Atlas.Orthogonal.hyperbolicExchange_fixed
#print axioms Atlas.Orthogonal.hyperbolicExchange_residual
#print axioms Atlas.Orthogonal.hyperbolicExchange_residual_finrank
#print axioms Atlas.Orthogonal.splitDExchange
#print axioms Atlas.Orthogonal.splitDExchange_residual_finrank
#print axioms Atlas.Orthogonal.hyperbolicExchange_ne_one
#print axioms Atlas.Orthogonal.splitDExchange_determinant
#print axioms Atlas.Orthogonal.splitDExchange_special
#print axioms Atlas.Orthogonal.splitDExchangeElement
#print axioms Atlas.Orthogonal.splitDExchangeElement_mem_reflections
#print axioms Atlas.Orthogonal.dicksonValue_splitDExchange
#print axioms Atlas.Orthogonal.splitDReflectionCharacter
#print axioms Atlas.Orthogonal.splitDReflectionCharacter_value
#print axioms Atlas.Orthogonal.splitDReflectionCharacter_surjective
#print axioms Atlas.Orthogonal.B2Exterior.wedge
#print axioms Atlas.Orthogonal.B2Exterior.pfaffian
#print axioms Atlas.Orthogonal.B2Exterior.pfaffian_apply
#print axioms Atlas.Orthogonal.B2Exterior.contraction
#print axioms Atlas.Orthogonal.B2Exterior.contraction_apply
#print axioms Atlas.Orthogonal.B2Exterior.symplecticCoordinates
#print axioms Atlas.Orthogonal.B2Exterior.contraction_wedge
#print axioms Atlas.Orthogonal.B2Exterior.pfaffian_wedge
#print axioms Atlas.Orthogonal.B2Exterior.fromB
#print axioms Atlas.Orthogonal.B2Exterior.fromB_contraction
#print axioms Atlas.Orthogonal.B2Exterior.fromB_pfaffian
#print axioms Atlas.Orthogonal.B2Exterior.kernelEquiv
#print axioms Atlas.Orthogonal.B2Exterior.kernelIsometry
#print axioms Atlas.Orthogonal.B2Exterior.first
#print axioms Atlas.Orthogonal.B2Exterior.second
#print axioms Atlas.Orthogonal.B2Exterior.compound
#print axioms Atlas.Orthogonal.B2Exterior.exteriorMap
#print axioms Atlas.Orthogonal.B2Exterior.exteriorMap_wedge
#print axioms Atlas.Orthogonal.B2Exterior.wedge_basis
#print axioms Atlas.Orthogonal.B2Exterior.exterior_ext
#print axioms Atlas.Orthogonal.B2Exterior.exteriorMap_mul
#print axioms Atlas.Orthogonal.B2Exterior.exteriorMap_one
#print axioms Atlas.Orthogonal.B2Exterior.pfaffian_exteriorMap
#print axioms Atlas.Orthogonal.B2Exterior.contraction_exteriorMap
#print axioms Atlas.Orthogonal.B2Exterior.symplecticMatrix
#print axioms Atlas.Orthogonal.B2Exterior.symplecticMatrix_one
#print axioms Atlas.Orthogonal.B2Exterior.symplecticMatrix_mul
#print axioms Atlas.Orthogonal.B2Exterior.symplecticMatrix_det
#print axioms Atlas.Orthogonal.B2Exterior.symplecticCoordinates_eq
#print axioms Atlas.Orthogonal.B2Exterior.symplecticCoordinates_surjective
#print axioms Atlas.Orthogonal.B2Exterior.symplecticMatrix_mulVec
#print axioms Atlas.Orthogonal.B2Exterior.symplectic_contraction
#print axioms Atlas.Orthogonal.B2Exterior.symplectic_pfaffian
#print axioms Atlas.Orthogonal.B2Exterior.kernelMap
#print axioms Atlas.Orthogonal.B2Exterior.kernelMap_mul
#print axioms Atlas.Orthogonal.B2Exterior.kernelMap_one
#print axioms Atlas.Orthogonal.B2Exterior.kernelAction
#print axioms Atlas.Orthogonal.B2Exterior.onB
#print axioms Atlas.Orthogonal.B2Exterior.onB_pfaffian
#print axioms Atlas.Orthogonal.B2Exterior.toOrthogonal
#print axioms Atlas.Orthogonal.B2Exterior.toOrthogonal_mem_elementary
#print axioms Atlas.Orthogonal.B2Exterior.toElementary
#print axioms Atlas.Orthogonal.B2Exterior.toElementary_coe
#print axioms Atlas.Orthogonal.B2Exterior.card_psp_eq_elementary
#print axioms Atlas.Orthogonal.B2Exterior.symplecticCoordinates_injective
#print axioms Atlas.Orthogonal.B2Exterior.symplecticMatrix_scalar_action
#print axioms Atlas.Orthogonal.B2Exterior.exteriorMap_scalar
#print axioms Atlas.Orthogonal.B2Exterior.toOrthogonal_eq_one_of_center
#print axioms Atlas.Orthogonal.B2Exterior.kernelMap_eq_of_toOrthogonal_eq_one
#print axioms Atlas.Orthogonal.B2Exterior.exteriorMap_eq_of_toOrthogonal_eq_one
#print axioms Atlas.Orthogonal.B2Exterior.wedge_eq_minor
#print axioms Atlas.Orthogonal.B2Exterior.scalar_of_exteriorMap_eq_id
#print axioms Atlas.Orthogonal.B2Exterior.scalar_of_toOrthogonal_eq_one
#print axioms Atlas.Orthogonal.B2Exterior.toOrthogonal_eq_one_iff_center
#print axioms Atlas.Orthogonal.B2Exterior.toOrthogonal_kernel
#print axioms Atlas.Orthogonal.B2Exterior.toElementary_kernel
#print axioms Atlas.Orthogonal.B2Exterior.fromPSp
#print axioms Atlas.Orthogonal.B2Exterior.fromPSp_projection
#print axioms Atlas.Orthogonal.B2Exterior.fromPSp_injective
#print axioms Atlas.Orthogonal.B2Exterior.fromPSp_bijective
#print axioms Atlas.Orthogonal.B2Exterior.pspEquivElementary
#print axioms Atlas.Orthogonal.B2Exterior.projectiveBEquivPSp
#print axioms Atlas.Orthogonal.B2Exterior.toElementary_surjective
#print axioms Atlas.Orthogonal.B2Exterior.toOrthogonal_range
#print axioms Atlas.Orthogonal.odd_rank_two_good
#print axioms Atlas.Orthogonal.projectiveB_two_simple
#print axioms Atlas.Orthogonal.elementaryB_two_perfect
#print axioms Atlas.Orthogonal.elementaryB_two_simple
#print axioms Atlas.Orthogonal.oddSpinorKernelB_two_simple
#print axioms Atlas.Orthogonal.projectiveB_simple_iff
#print axioms Atlas.Orthogonal.projectiveB_noncommutative
#print axioms Atlas.Orthogonal.B2_three_simple
#print axioms Atlas.Orthogonal.B2_two_not_simple
#print axioms Atlas.Orthogonal.B2_three_order
#print axioms Atlas.Orthogonal.B2_two_order
#print axioms Atlas.Quadratic.siegel_residual_le_span
#print axioms Atlas.Quadratic.siegel_isotropic_residual
#print axioms Atlas.Quadratic.siegel_residual_finrank_le_two
#print axioms Atlas.Quadratic.dicksonParity_siegel_isotropic
#print axioms Atlas.Quadratic.exists_anisotropic_perpendicular_pair
#print axioms Atlas.Quadratic.perpendicular_hyperbolic_partner_of_not_mem_span
#print axioms Atlas.Quadratic.hyperbolic_pair_in_perpendicular_all_char
#print axioms Atlas.Quadratic.exists_singular_perpendicular_witness_all_char
#print axioms Atlas.Orthogonal.evenReflectionSubgroup
#print axioms Atlas.Orthogonal.reflection_pair_mem_even
#print axioms Atlas.Orthogonal.evenReflection_le_reflection
#print axioms Atlas.Orthogonal.evenReflectionSubgroup_normal
#print axioms Atlas.Orthogonal.evenReflection_dickson_zero
#print axioms Atlas.Orthogonal.mem_evenReflection_iff
#print axioms Atlas.Orthogonal.reflectionDicksonCharacter_kernel_image
#print axioms Atlas.Orthogonal.reflectionDicksonCharacter_surjective
#print axioms Atlas.Orthogonal.reflectionParityQuotientEquiv
#print axioms Atlas.Orthogonal.card_evenReflection_mul_two
#print axioms Atlas.Orthogonal.dicksonValue_reflection_mul
#print axioms Atlas.Orthogonal.dicksonValue_reflection
#print axioms Atlas.Orthogonal.dicksonValue_siegel
#print axioms Atlas.Orthogonal.siegel_residual_finrank_zero_or_two
#print axioms Atlas.Orthogonal.isotropic_parameter_anisotropic_sum_stable
#print axioms Atlas.Orthogonal.anisotropic_siegel_mem_reflections
#print axioms Atlas.Orthogonal.siegel_mem_reflections_stable
#print axioms Atlas.Orthogonal.elementary_le_reflections_stable
#print axioms Atlas.Orthogonal.dicksonValue_elementary_stable
#print axioms Atlas.Orthogonal.elementaryD_le_reflections_stable
#print axioms Atlas.Orthogonal.dicksonValue_elementaryD_stable
#print axioms Atlas.Orthogonal.elementaryDReflectionHom
#print axioms Atlas.Orthogonal.elementaryDReflectionHom_injective
#print axioms Atlas.Orthogonal.elementaryDReflectionHom_character
#print axioms Atlas.Orthogonal.elementaryD_le_evenReflections_stable
#print axioms Atlas.Orthogonal.elementary_transport_independent_all_char
#print axioms Atlas.Orthogonal.elementary_singular_transport_all_char
#print axioms Atlas.Orthogonal.elementary_pair_transport_all_char
#print axioms Atlas.Orthogonal.elementaryD_singular_transport_all_char
#print axioms Atlas.Orthogonal.elementaryD_pair_transport_all_char
#print axioms Atlas.Orthogonal.reflectionSubgroup_singular_transport
#print axioms Atlas.Orthogonal.elementaryReflection_pair_transport
#print axioms Atlas.Orthogonal.complementLift_reflection
#print axioms Atlas.Orthogonal.complementLift_mem_elementaryReflection
#print axioms Atlas.Orthogonal.isometryTransport_mem_elementaryReflection
#print axioms Atlas.Orthogonal.elementary_sup_reflectionsD_eq_top
#print axioms Atlas.Orthogonal.reflectionSubgroupD_eq_top_stable
#print axioms Atlas.Orthogonal.elementary_transport_equal_value_char_two
#print axioms Atlas.Orthogonal.even_reflection_pair_mem_elementary
#print axioms Atlas.Orthogonal.evenReflection_le_elementary_char_two
#print axioms Atlas.Orthogonal.evenReflectionD_eq_elementary
#print axioms Atlas.Orthogonal.dicksonValue_mul_D_stable
#print axioms Atlas.Orthogonal.fullDicksonD
#print axioms Atlas.Orthogonal.fullDicksonD_value
#print axioms Atlas.Orthogonal.fullDicksonD_restrict_reflections
#print axioms Atlas.Orthogonal.fullDicksonD_exchange
#print axioms Atlas.Orthogonal.fullDicksonD_surjective
#print axioms Atlas.Orthogonal.fullDicksonD_kernel_evenReflection
#print axioms Atlas.Orthogonal.fullDicksonD_kernel_elementary
#print axioms Atlas.Orthogonal.mem_elementaryD_iff_dickson_zero
#print axioms Atlas.Orthogonal.card_evenElementaryD_mul_two
#print axioms Atlas.Orthogonal.card_evenElementaryD
#print axioms Atlas.Orthogonal.card_evenProjectiveD
#print axioms Atlas.Orthogonal.siegel_mem_commutator_of_translation
#print axioms Atlas.Orthogonal.singular_siegel_mem_commutator
#print axioms Atlas.Orthogonal.exists_three_singular_sum
#print axioms Atlas.Orthogonal.complement_perpendicular_pair_all_char
#print axioms Atlas.Orthogonal.root_mem_commutator_all_char
#print axioms Atlas.Orthogonal.elementary_perfect_of_complements_all_char
#print axioms Atlas.Orthogonal.elementaryD_perfect_all_char
#print axioms Atlas.Orthogonal.elementaryD_perpendicular_stabilizer_transport
#print axioms Atlas.Orthogonal.singular_stabilizerD_perpendicular_transitive
#print axioms Atlas.Orthogonal.exists_singular_nonperpendicular_connector_all_char
#print axioms Atlas.Orthogonal.exists_singular_perpendicular_connectorD
#print axioms Atlas.Orthogonal.singularPointsD_perpendicular_connector
#print axioms Atlas.Orthogonal.singularPointsD_nonperpendicular_connector
#print axioms Atlas.Orthogonal.singularPointsD_pretransitive
#print axioms Atlas.Orthogonal.singularPointsD_primitive
#print axioms Atlas.Orthogonal.projectiveSingularD_faithful
#print axioms Atlas.Orthogonal.projectiveSingularD_primitive
#print axioms Atlas.Orthogonal.projectiveRootSubgroup
#print axioms Atlas.Orthogonal.projectiveRoot_commutative
#print axioms Atlas.Orthogonal.projectiveRoot_le_point_stabilizer
#print axioms Atlas.Orthogonal.projectiveRoot_normal_point_stabilizer
#print axioms Atlas.Orthogonal.projectiveRoot_normalClosure_eq_top
#print axioms Atlas.Orthogonal.projectiveRootD_normalClosure_eq_top
#print axioms Atlas.Orthogonal.projectiveD_nontrivial_all_char
#print axioms Atlas.Orthogonal.projectiveD_perfect_all_char
#print axioms Atlas.Orthogonal.projectiveD_simple_all_char
#print axioms Atlas.Orthogonal.projectiveD_noncommutative_all_char
#print axioms Atlas.Orthogonal.evenD_order_denominator
#print axioms Atlas.Orthogonal.card_projectiveD_all_char_mul_gcd
#print axioms Atlas.Orthogonal.card_projectiveD_all_char
#print axioms Atlas.Orthogonal.card_projectiveD3_two
#print axioms Atlas.Orthogonal.card_projectiveD4_two
#print axioms Atlas.Orthogonal.elementaryD_eq_commutator_even
#print axioms Atlas.Orthogonal.fullDicksonD_kernel_eq_commutator
#print axioms Atlas.Orthogonal.evenDElementaryKernelEquiv
#print axioms Atlas.Orthogonal.evenDElementaryKernelEquiv_coe
#print axioms Atlas.Orthogonal.evenDProjectiveKernelEquiv
#print axioms Atlas.Orthogonal.evenDProjectiveKernelEquiv_projection
#print axioms Atlas.Orthogonal.evenDProjectiveKernelEquiv_projection_coe
#print axioms Atlas.Orthogonal.fullDicksonD_kernel_perfect
#print axioms Atlas.Orthogonal.fullDicksonD_kernel_simple
#print axioms Atlas.Orthogonal.fullDicksonD_kernel_noncommutative
#print axioms Atlas.Orthogonal.b2BinaryEquivSymmetric
#print axioms Atlas.Orthogonal.b2Binary_commutator_map
#print axioms Atlas.Orthogonal.b2BinaryDerivedEquivAlternating
#print axioms Atlas.Orthogonal.card_b2Binary
#print axioms Atlas.Orthogonal.b2Binary_not_simple
#print axioms Atlas.Orthogonal.card_b2BinaryDerived
#print axioms Atlas.Orthogonal.b2BinaryDerived_simple
#print axioms Atlas.Orthogonal.b2BinaryDerived_noncommutative
#print axioms Atlas.Orthogonal.DPlus
#print axioms Atlas.Orthogonal.DPlus_order_numerator
#print axioms Atlas.Orthogonal.DPlus_order_denominator
#print axioms Atlas.Orthogonal.DPlus_order
#print axioms Atlas.Orthogonal.DPlus_admissible
#print axioms Atlas.Orthogonal.DPlus_order_denominator_positive
#print axioms Atlas.Orthogonal.DPlus_order_numerator_positive
#print axioms Atlas.Orthogonal.DPlus_finite
#print axioms Atlas.Orthogonal.DPlus_card_mul_denominator
#print axioms Atlas.Orthogonal.DPlus_order_divisibility
#print axioms Atlas.Orthogonal.DPlus_card
#print axioms Atlas.Orthogonal.DPlus_simple
#print axioms Atlas.Orthogonal.DPlus_noncommutative
#print axioms Atlas.Orthogonal.DPlus_perfect
#print axioms Atlas.Orthogonal.DPlus_elementary_perfect
#print axioms Atlas.Orthogonal.DPlus_faithful
#print axioms Atlas.Orthogonal.DPlus_primitive
#print axioms Atlas.Orthogonal.DPlus_transitive
#print axioms Atlas.Orthogonal.DPlus_scalar_eq_center
#print axioms Atlas.Orthogonal.DPlus_roots_normal_generate
#print axioms Atlas.Orthogonal.DPlus_simple_iff
#print axioms Atlas.Orthogonal.DPlus_elementary_eq_derived
#print axioms Atlas.Orthogonal.DPlus_full_order
#print axioms Atlas.Orthogonal.DPlus_elementary_order_exact
#print axioms Atlas.Orthogonal.DPlus_elementary_order
#print axioms Atlas.Orthogonal.DPlus_elementary_index
#print axioms Atlas.Orthogonal.DPlus_center_order_exact
#print axioms Atlas.Orthogonal.DPlus_scalar_order_exact
#print axioms Atlas.Orthogonal.DPlus_center_order
#print axioms Atlas.Orthogonal.DPlus_odd_intrinsic
#print axioms Atlas.Orthogonal.DPlus_even_intrinsic
#print axioms Atlas.TypeDConstruction
#print axioms Atlas.typeD_construction
#print axioms Atlas.exists_typeD
#print axioms Atlas.typeD_prime_power
#print axioms Atlas.Orthogonal.orthogonal_gcd_two_odd
#print axioms Atlas.Orthogonal.orthogonal_gcd_two_even
#print axioms Atlas.Orthogonal.card_elementaryD_all_char_mul_gcd_two
#print axioms Atlas.Orthogonal.elementaryD_index_all_char
#print axioms Atlas.Orthogonal.card_elementaryD_center_all_char_mul_gcd_two
#print axioms Atlas.Orthogonal.elementaryD_scalar_eq_center
#print axioms Atlas.Orthogonal.projectiveDQuotientCenterEquiv
#print axioms Atlas.Orthogonal.card_elementaryD_all_char
#print axioms Atlas.Orthogonal.card_elementaryD_scalar_all_char_mul_gcd_two
#print axioms Atlas.Orthogonal.card_elementaryD_center_all_char
#print axioms Atlas.Orthogonal.fullDicksonKernelElementaryEquiv
#print axioms Atlas.Orthogonal.fieldEquivDicksonKernelD
#print axioms Atlas.Orthogonal.fieldEquivDicksonKernelD_full
#print axioms Atlas.Orthogonal.fieldEquivDicksonKernelD_elementary
#print axioms Atlas.Orthogonal.fieldEquivDicksonKernelD_projective
#print axioms Atlas.Orthogonal.DPlus_fieldEquiv
#print axioms Atlas.Orthogonal.DPlus_fieldEquiv_projection
#print axioms Atlas.Orthogonal.fieldEquivElementaryD_refl
#print axioms Atlas.Orthogonal.fieldEquivElementaryD_trans
#print axioms Atlas.Orthogonal.DPlus_fieldEquiv_refl
#print axioms Atlas.Orthogonal.DPlus_fieldEquiv_trans
#print axioms Atlas.Orthogonal.DPlus_fieldEquiv_symm
#print axioms Atlas.Orthogonal.DPlus_equiv_of_card_eq
#print axioms Atlas.Orthogonal.Checks.d4_three_order
#print axioms Atlas.Orthogonal.Checks.d4_four_order
#print axioms Atlas.Orthogonal.Checks.d4_three_simple
#print axioms Atlas.Orthogonal.Checks.d4_four_simple
#print axioms Atlas.Orthogonal.semilinearResidualEquiv
#print axioms Atlas.Orthogonal.residual_finrank_semilinear_transport
#print axioms Atlas.Orthogonal.dicksonValue_semilinear_transport
#print axioms Atlas.Orthogonal.residual_finrank_fieldEquivFullD
#print axioms Atlas.Orthogonal.dicksonValue_fieldEquivFullD
#print axioms Atlas.Orthogonal.fullDicksonD_field_transport
#print axioms Atlas.Orthogonal.D3Exterior.coordinates
#print axioms Atlas.Orthogonal.D3Exterior.coordinates_form
#print axioms Atlas.Orthogonal.D3Exterior.exteriorAction
#print axioms Atlas.Orthogonal.D3Exterior.onD
#print axioms Atlas.Orthogonal.D3Exterior.onD_form
#print axioms Atlas.Orthogonal.D3Exterior.toOrthogonal
#print axioms Atlas.Orthogonal.D3Exterior.scalar_of_exteriorMap_scalar
#print axioms Atlas.Orthogonal.D3Exterior.toOrthogonal_scalar_iff
#print axioms Atlas.Orthogonal.D3Exterior.toOrthogonal_eq_one_iff
#print axioms Atlas.Orthogonal.D3Exterior.toOrthogonal_mem_elementary
#print axioms Atlas.Orthogonal.D3Exterior.toElementary
#print axioms Atlas.Orthogonal.D3Exterior.toProjective
#print axioms Atlas.Orthogonal.D3Exterior.toProjective_eq_one_iff_center
#print axioms Atlas.Orthogonal.D3Exterior.toProjective_kernel
#print axioms Atlas.Orthogonal.D3Exterior.projectiveHom
#print axioms Atlas.Orthogonal.D3Exterior.projectiveHom_projection
#print axioms Atlas.Orthogonal.D3Exterior.projectiveHom_injective
#print axioms Atlas.Orthogonal.D3Exterior.gcd_four_cube_sub_one
#print axioms Atlas.Orthogonal.D3Exterior.card_psl_four_eq_projectiveD_three
#print axioms Atlas.Orthogonal.D3Exterior.projectiveHom_surjective
#print axioms Atlas.Orthogonal.D3Exterior.projectiveEquiv
#print axioms Atlas.Orthogonal.D3Exterior.projectiveEquiv_projection
#print axioms Atlas.Orthogonal.D3Exterior.d3EquivPSL4
#print axioms Atlas.Orthogonal.D3Exterior.image_mul_center
#print axioms Atlas.Orthogonal.D3Exterior.commutator_le_image
#print axioms Atlas.Orthogonal.D3Exterior.toElementary_surjective
#print axioms Atlas.Orthogonal.D3Exterior.toOrthogonal_range
#print axioms Atlas.Orthogonal.D2Matrix.Mat
#print axioms Atlas.Orthogonal.D2Matrix.PairSL
#print axioms Atlas.Orthogonal.D2Matrix.coordinates
#print axioms Atlas.Orthogonal.D2Matrix.coordinates_det
#print axioms Atlas.Orthogonal.D2Matrix.determinantForm
#print axioms Atlas.Orthogonal.D2Matrix.determinantForm_apply
#print axioms Atlas.Orthogonal.D2Matrix.coordinatesIsometry
#print axioms Atlas.Orthogonal.D2Matrix.matrixAction
#print axioms Atlas.Orthogonal.D2Matrix.matrixAction_det
#print axioms Atlas.Orthogonal.D2Matrix.onD
#print axioms Atlas.Orthogonal.D2Matrix.onD_form
#print axioms Atlas.Orthogonal.D2Matrix.toOrthogonal
#print axioms Atlas.Orthogonal.D2Matrix.toOrthogonal_coordinates
#print axioms Atlas.Orthogonal.D2Matrix.toOrthogonal_eq_one_iff
#print axioms Atlas.Orthogonal.D2Matrix.toOrthogonal_kernel_iff
#print axioms Atlas.Orthogonal.D2Matrix.toOrthogonal_kernel_scalar
#print axioms Atlas.Orthogonal.D2Matrix.matrixAction_scalar_implies_centers
#print axioms Atlas.Orthogonal.D2Matrix.toOrthogonal_scalar_implies_centers
#print axioms Atlas.Orthogonal.D2Matrix.toOrthogonal_scalar_iff_centers
#print axioms Atlas.Orthogonal.D2Matrix.left_upper_root
#print axioms Atlas.Orthogonal.D2Matrix.left_lower_root
#print axioms Atlas.Orthogonal.D2Matrix.right_upper_root
#print axioms Atlas.Orthogonal.D2Matrix.right_lower_root
#print axioms Atlas.Orthogonal.D2Matrix.left_mem_elementary
#print axioms Atlas.Orthogonal.D2Matrix.right_mem_elementary
#print axioms Atlas.Orthogonal.D2Matrix.toOrthogonal_mem_elementary
#print axioms Atlas.Orthogonal.D2Matrix.image_le_elementary
#print axioms Atlas.Orthogonal.D2Matrix.standard_siegel_image
#print axioms Atlas.Orthogonal.D2Matrix.singular_image_orbit
#print axioms Atlas.Orthogonal.D2Matrix.siegel_mem_image
#print axioms Atlas.Orthogonal.D2Matrix.elementary_le_image
#print axioms Atlas.MatrixTwo.firstColumnMatrix
#print axioms Atlas.MatrixTwo.firstColumnMatrix_det
#print axioms Atlas.MatrixTwo.columnCompletion
#print axioms Atlas.MatrixTwo.columnCompletion_first
#print axioms Atlas.MatrixTwo.singular_nonzero_factor
#print axioms Atlas.MatrixTwo.E11
#print axioms Atlas.MatrixTwo.singular_nonzero_SL2_orbit
#print axioms Atlas.Orthogonal.D2Matrix.toOrthogonal_range
#print axioms Atlas.Orthogonal.D2Matrix.toElementary
#print axioms Atlas.Orthogonal.D2Matrix.toElementary_surjective
#print axioms Atlas.Orthogonal.D2Matrix.toProjective
#print axioms Atlas.Orthogonal.D2Matrix.toProjective_surjective
#print axioms Atlas.Orthogonal.D2Matrix.toProjective_eq_one_iff_centers
#print axioms Atlas.Orthogonal.D2Matrix.toProjective_kernel
#print axioms Atlas.Orthogonal.D2Matrix.productProjection
#print axioms Atlas.Orthogonal.D2Matrix.productProjection_surjective
#print axioms Atlas.Orthogonal.D2Matrix.projective_kernels_eq
#print axioms Atlas.Orthogonal.D2Matrix.projectiveEquivProduct
#print axioms Atlas.Orthogonal.D2Matrix.projectiveEquivProduct_projection
#print axioms Atlas.Orthogonal.D2Matrix.card_projectiveD_two_eq_psl_square
#print axioms Atlas.Orthogonal.D2Matrix.card_projectiveD_two_mul_gcd_square
#print axioms Atlas.Orthogonal.D2Matrix.projectiveD_two_order_divisibility
#print axioms Atlas.Orthogonal.D2Matrix.card_projectiveD_two
#print axioms Atlas.Orthogonal.B1Conjugation.Mat
#print axioms Atlas.Orthogonal.B1Conjugation.SL
#print axioms Atlas.Orthogonal.B1Conjugation.TraceZero
#print axioms Atlas.Orthogonal.B1Conjugation.coordinates
#print axioms Atlas.Orthogonal.B1Conjugation.coordinates_form
#print axioms Atlas.Orthogonal.B1Conjugation.conjugation_trace
#print axioms Atlas.Orthogonal.B1Conjugation.kernelMap
#print axioms Atlas.Orthogonal.B1Conjugation.kernelMap_mul
#print axioms Atlas.Orthogonal.B1Conjugation.kernelMap_one
#print axioms Atlas.Orthogonal.B1Conjugation.kernelAction
#print axioms Atlas.Orthogonal.B1Conjugation.onB
#print axioms Atlas.Orthogonal.B1Conjugation.onB_coordinates
#print axioms Atlas.Orthogonal.B1Conjugation.onB_form
#print axioms Atlas.Orthogonal.B1Conjugation.toOrthogonal
#print axioms Atlas.Orthogonal.B1Conjugation.scalar_commutation
#print axioms Atlas.Orthogonal.B1Conjugation.scalar_action_implies_center
#print axioms Atlas.Orthogonal.B1Conjugation.toOrthogonal_eq_one_of_center
#print axioms Atlas.Orthogonal.B1Conjugation.toOrthogonal_eq_one_iff_center
#print axioms Atlas.Orthogonal.B1Conjugation.toOrthogonal_kernel
#print axioms Atlas.Orthogonal.B1Conjugation.standard_siegel_image
#print axioms Atlas.Orthogonal.B1Conjugation.lower_transvection_root
#print axioms Atlas.Orthogonal.B1Conjugation.toOrthogonal_mem_elementary
#print axioms Atlas.Orthogonal.B1Conjugation.singular_line_orbit
#print axioms Atlas.Orthogonal.B1Conjugation.siegel_mem_image
#print axioms Atlas.Orthogonal.B1Conjugation.toOrthogonal_range
#print axioms Atlas.Orthogonal.B1Conjugation.toElementary
#print axioms Atlas.Orthogonal.B1Conjugation.toElementary_surjective
#print axioms Atlas.Orthogonal.B1Conjugation.toElementary_kernel
#print axioms Atlas.Orthogonal.B1Conjugation.elementaryEquivPSL
#print axioms Atlas.Orthogonal.B1Conjugation.elementaryScalar_eq_bot
#print axioms Atlas.Orthogonal.B1Conjugation.projectiveEquivPSL
#print axioms Atlas.Orthogonal.B1Conjugation.elementaryEquivPSL_projection
#print axioms Atlas.Orthogonal.B1Conjugation.projectiveEquivPSL_projection
#print axioms Atlas.MatrixTwo.traceZero_singular_SL2_line
#print axioms Atlas.InvolutionClasses
#print axioms Atlas.k2
#print axioms Atlas.involutionClassesEquiv
#print axioms Atlas.k2_mulEquiv
#print axioms Atlas.not_nonempty_mulEquiv_of_k2_ne
#print axioms Atlas.center_eq_bot_of_two_transitive
#print axioms Atlas.finite_field_binary_represents
#print axioms Atlas.finite_field_sum_two_squares
#print axioms Atlas.Quadratic.weighted_units_represents
#print axioms Atlas.Quadratic.finite_nondegenerate_represents
#print axioms Atlas.Quadratic.binaryForm
#print axioms Atlas.Quadratic.binaryForm_apply
#print axioms Atlas.Quadratic.binaryNormalizationLinear
#print axioms Atlas.Quadratic.binaryNormalizationIsometry
#print axioms Atlas.Quadratic.finite_binary_normalization
#print axioms Atlas.Quadratic.diagonalForm
#print axioms Atlas.Quadratic.splitFirstTwo
#print axioms Atlas.Quadratic.diagonalSplitTwo
#print axioms Atlas.Quadratic.diagonalChangeTwo
#print axioms Atlas.Quadratic.diagonalCons
#print axioms Atlas.Quadratic.normalWeights
#print axioms Atlas.Quadratic.finite_diagonal_normalization
#print axioms Atlas.Quadratic.normalWeightsSquareEquiv
#print axioms Atlas.Quadratic.finite_diagonal_isometry_of_product_square
#print axioms Atlas.Quadratic.finite_diagonal_isometry_of_square_ratio
#print axioms Atlas.Quadratic.weighted_units_eq_diagonal
#print axioms Atlas.Quadratic.finite_unit_diagonal_normalization
#print axioms Atlas.Quadratic.finite_unit_diagonal_isometry_of_square_ratio
#print axioms Atlas.LinearInvolution.plus
#print axioms Atlas.LinearInvolution.minus
#print axioms Atlas.LinearInvolution.mem_plus
#print axioms Atlas.LinearInvolution.mem_minus
#print axioms Atlas.LinearInvolution.isCompl
#print axioms Atlas.LinearInvolution.decomposition
#print axioms Atlas.LinearInvolution.orthogonal
#print axioms Atlas.LinearInvolution.decomposition_action
#print axioms Atlas.LinearInvolution.plus_nondegenerate
#print axioms Atlas.LinearInvolution.minus_nondegenerate
#print axioms Atlas.LinearInvolution.finrank_plus_add_minus
#print axioms Atlas.LinearInvolution.conjugator
#print axioms Atlas.LinearInvolution.conjugator_decomposition
#print axioms Atlas.LinearInvolution.conjugator_intertwines
#print axioms Atlas.LinearInvolution.decomposition_bilinear
#print axioms Atlas.LinearInvolution.conjugator_preserves
#print axioms Atlas.AlternatingForm.squareMinusOne_twisted_symmetric
#print axioms Atlas.AlternatingForm.squareMinusOne_nonzero_norm
#print axioms Atlas.AlternatingForm.squareMinusOne_norm_combination
#print axioms Atlas.AlternatingForm.squareMinusOne_exists_normalized
#print axioms Atlas.AlternatingForm.squareMinusOnePlane
#print axioms Atlas.AlternatingForm.squareMinusOnePlane_stable
#print axioms Atlas.AlternatingForm.squareMinusOnePlaneCoordinates
#print axioms Atlas.AlternatingForm.squareMinusOnePlane_finrank
#print axioms Atlas.AlternatingForm.squareMinusOnePlane_nondegenerate
#print axioms Atlas.AlternatingForm.squareMinusOne_complement_stable
#print axioms Atlas.AlternatingForm.squareMinusOne_stable_plane
#print axioms Atlas.Orthogonal.B
#print axioms Atlas.Orthogonal.B_order_numerator
#print axioms Atlas.Orthogonal.B_order_denominator
#print axioms Atlas.Orthogonal.B_order
#print axioms Atlas.Orthogonal.B_admissible
#print axioms Atlas.Orthogonal.B_order_denominator_positive
#print axioms Atlas.Orthogonal.B_order_numerator_positive
#print axioms Atlas.Orthogonal.B_finite
#print axioms Atlas.Orthogonal.B_card_mul_denominator
#print axioms Atlas.Orthogonal.B_order_divisibility
#print axioms Atlas.Orthogonal.B_card
#print axioms Atlas.Orthogonal.B_good
#print axioms Atlas.Orthogonal.B_card_mul_denominator_all_rank
#print axioms Atlas.Orthogonal.B_order_divisibility_all_rank
#print axioms Atlas.Orthogonal.B_card_all_rank
#print axioms Atlas.Orthogonal.B_simple_iff_all_rank
#print axioms Atlas.Orthogonal.B_simple_all_rank
#print axioms Atlas.Orthogonal.B_elementary_perfect_all_rank
#print axioms Atlas.Orthogonal.B_perfect_all_rank
#print axioms Atlas.Orthogonal.B_noncommutative_all_rank
#print axioms Atlas.Orthogonal.B_simple_iff
#print axioms Atlas.Orthogonal.B_simple
#print axioms Atlas.Orthogonal.B_noncommutative
#print axioms Atlas.Orthogonal.B_elementary_perfect
#print axioms Atlas.Orthogonal.B_perfect
#print axioms Atlas.Orthogonal.B_scalar_eq_bot
#print axioms Atlas.Orthogonal.B_elementaryEquiv
#print axioms Atlas.Orthogonal.B_center_eq_bot
#print axioms Atlas.Orthogonal.B_elementary_order
#print axioms Atlas.Orthogonal.B_odd_intrinsic
#print axioms Atlas.Orthogonal.B_even_intrinsic
#print axioms Atlas.Orthogonal.B_generated_by_siegel
#print axioms Atlas.Orthogonal.B_fieldEquiv
#print axioms Atlas.Orthogonal.B_fieldEquiv_projection
#print axioms Atlas.typeB_construction
#print axioms Atlas.exists_typeB
#print axioms Atlas.typeB_prime_power
#print axioms Atlas.Orthogonal.fieldEquivElementaryB_refl
#print axioms Atlas.Orthogonal.fieldEquivElementaryB_trans
#print axioms Atlas.Orthogonal.B_fieldEquiv_refl
#print axioms Atlas.Orthogonal.B_fieldEquiv_trans
#print axioms Atlas.Orthogonal.B_fieldEquiv_symm
#print axioms Atlas.Orthogonal.B_equiv_of_card_eq
#print axioms Atlas.Orthogonal.B_faithful
#print axioms Atlas.Orthogonal.B_odd_transitive
#print axioms Atlas.Orthogonal.B_odd_elementary_primitive
#print axioms Atlas.Orthogonal.B_roots_abelian
#print axioms Atlas.Orthogonal.B_roots_normal_in_stabilizer
#print axioms Atlas.Orthogonal.B_odd_roots_normal_generate
#print axioms Atlas.Orthogonal.B_elementary_card_mul_denominator
#print axioms Atlas.Orthogonal.B_elementary_index
#print axioms Atlas.Orthogonal.B_center_order
#print axioms Atlas.Orthogonal.B_scalar_order
#print axioms Atlas.Orthogonal.B_elementary_eq_derived
#print axioms Atlas.Orthogonal.B_scalar_eq_bot_all_rank
#print axioms Atlas.Orthogonal.B_elementaryEquiv_all_rank
#print axioms Atlas.Orthogonal.B_elementary_order_all_rank
#print axioms Atlas.typeB_all_ranks_construction
#print axioms Atlas.exists_typeB_all_ranks
#print axioms Atlas.typeB_prime_power_all_ranks
#print axioms Atlas.Orthogonal.B1_two_order
#print axioms Atlas.Orthogonal.B1_three_order
#print axioms Atlas.Orthogonal.B1_two_not_simple
#print axioms Atlas.Orthogonal.B1_three_not_simple
#print axioms Atlas.Orthogonal.B1_five_simple
#print axioms Atlas.Orthogonal.psl_two_center_eq_bot
#print axioms Atlas.Orthogonal.elementaryB_one_center_eq_bot
#print axioms Atlas.Orthogonal.card_elementaryB_one_eq_oddKernel
#print axioms Atlas.Orthogonal.elementaryB_one_to_oddKernel
#print axioms Atlas.Orthogonal.elementaryB_one_to_oddKernel_injective
#print axioms Atlas.Orthogonal.elementaryB_one_to_oddKernel_surjective
#print axioms Atlas.Orthogonal.elementaryB_one_eq_intrinsicKernel
#print axioms Atlas.Orthogonal.elementaryB_one_kernelEquiv
#print axioms Atlas.Comparisons.Classical.b1EquivA1
#print axioms Atlas.Comparisons.Classical.evenBEquivC
#print axioms Atlas.Comparisons.Classical.b2EquivC2
#print axioms Atlas.Comparisons.Classical.d2EquivProduct
#print axioms Atlas.Comparisons.Classical.d3EquivA3
#print axioms Atlas.Comparisons.Classical.bFieldEquiv
#print axioms Atlas.Comparisons.Classical.dFieldEquiv
#print axioms Atlas.Comparisons.Classical.oddB_card_eq_C
#print axioms Atlas.AlternatingForm.even_finrank
#print axioms Atlas.AlternatingForm.exists_half_finrank
#print axioms Atlas.AlternatingForm.isometry_exists_of_finrank_eq
#print axioms Atlas.AlternatingForm.involution_isometry_exists
#print axioms Atlas.AlternatingForm.involution_conjugacy
#print axioms Atlas.AlternatingForm.squareMinusOneComplementOperator
#print axioms Atlas.AlternatingForm.squareMinusOneComplementOperator_square
#print axioms Atlas.AlternatingForm.squareMinusOneComplementOperator_preserves
#print axioms Atlas.AlternatingForm.squareMinusOne_split_operator
#print axioms Atlas.AlternatingForm.squareMinusOne_isometry_exists
#print axioms Atlas.AlternatingForm.squareMinusOne_conjugacy
#print axioms Atlas.Quadratic.diagonal_toMatrix
#print axioms Atlas.Quadratic.diagonal_discr
#print axioms Atlas.Quadratic.discr_ratio_isSquare_of_isometry
#print axioms Atlas.Quadratic.finite_diagonal_isometry_iff_square_ratio
#print axioms Atlas.Quadratic.associated_separating_of_polar_nondegenerate
#print axioms Atlas.Quadratic.discr_ne_zero_of_nondegenerate
#print axioms Atlas.Quadratic.finite_nondegenerate_diagonalization
#print axioms Atlas.Quadratic.finite_nondegenerate_isometry_iff_discr_square
#print axioms Atlas.Quadratic.basisRepr_discr
#print axioms Atlas.Quadratic.finite_nondegenerate_isometry_iff_basis_discr_square
#print axioms Atlas.Quadratic.associated_nondegenerate
#print axioms Atlas.Quadratic.discriminantClass
#print axioms Atlas.Quadratic.discriminantClass_basis
#print axioms Atlas.Quadratic.square_ratio_of_squareClass_eq
#print axioms Atlas.Quadratic.finite_nondegenerate_isometry_of_discriminantClass
#print axioms Atlas.Quadratic.involution_residual_eq_minus
#print axioms Atlas.Quadratic.involution_wallForm_apply
#print axioms Atlas.Quadratic.involution_wallForm_eq_associated
#print axioms Atlas.Quadratic.involution_restricted_discr_ne_zero
#print axioms Atlas.Quadratic.involution_wallDeterminantClass
#print axioms Atlas.LinearInvolution.determinant
#print axioms Atlas.LinearInvolution.even_finrank_minus_of_det_one
#print axioms Atlas.LinearInvolution.finrank_minus_pos_of_ne_id
#print axioms Atlas.LinearInvolution.two_le_finrank_minus_of_det_one
#print axioms Atlas.kernel_conjugator_of_centralizer_image
#print axioms Atlas.isConj_in_kernel_iff
#print axioms Atlas.Orthogonal.reflectionElement_commute_of_minus
#print axioms Atlas.Orthogonal.involution_minus_represents
#print axioms Atlas.Orthogonal.involution_centralizer_correction
#print axioms Atlas.Symplectic.negativeIdentity
#print axioms Atlas.Symplectic.negativeIdentity_apply
#print axioms Atlas.Symplectic.negativeIdentity_central
#print axioms Atlas.Symplectic.negativeIdentity_square
#print axioms Atlas.Symplectic.projection_negativeIdentity
#print axioms Atlas.Symplectic.center_iff_eq_one_or_negativeIdentity
#print axioms Atlas.Symplectic.projection_square_eq_one_iff
#print axioms Atlas.Symplectic.projection_eq_iff_signed
#print axioms Atlas.Symplectic.projection_isConj_iff_signed
#print axioms Atlas.Symplectic.negativeIdentity_ne_one
#print axioms Atlas.Symplectic.projection_order_two_iff
#print axioms Atlas.Symplectic.minusDimension
#print axioms Atlas.Symplectic.isConj_of_linear_intertwiner
#print axioms Atlas.Symplectic.square_one_isConj_of_minusDimension_eq
#print axioms Atlas.Symplectic.square_negativeIdentity_isConj
#print axioms Atlas.Symplectic.minusEquivOfIntertwiner
#print axioms Atlas.Symplectic.minusDimension_eq_of_isConj
#print axioms Atlas.Symplectic.square_one_isConj_iff_minusDimension_eq
#print axioms Atlas.Symplectic.signRepresentative
#print axioms Atlas.Symplectic.signRepresentative_apply
#print axioms Atlas.Symplectic.signRepresentative_square
#print axioms Atlas.Symplectic.complexRepresentative
#print axioms Atlas.Symplectic.complexRepresentative_apply_left
#print axioms Atlas.Symplectic.complexRepresentative_apply_right
#print axioms Atlas.Symplectic.complexRepresentative_square
#print axioms Atlas.Symplectic.complexRepresentative_not_central
#print axioms Atlas.Orthogonal.B_center_eq_bot_all_rank
#print axioms Atlas.Orthogonal.B_scalar_eq_center_all_rank
#print axioms Atlas.Orthogonal.B_center_order_all_rank
#print axioms Atlas.Orthogonal.B_elementary_card_mul_denominator_all_rank
#print axioms Atlas.Orthogonal.B_elementary_index_all_rank
#print axioms Atlas.Orthogonal.B_odd_intrinsic_all_rank
#print axioms Atlas.Orthogonal.B_elementary_eq_derived_all_rank
#print axioms Atlas.Orthogonal.B_quotientCenterEquiv_all_rank
#print axioms Atlas.Orthogonal.B_equiv_of_card_eq_all_rank
#print axioms Atlas.TypeBStructuralConstruction
#print axioms Atlas.typeB_structural_construction
#print axioms Atlas.typeB_prime_power_structural
#print axioms Atlas.exists_typeB_structural
#print axioms Atlas.Symplectic.signSupport
#print axioms Atlas.Symplectic.signMinusEquiv
#print axioms Atlas.Symplectic.signRepresentative_minusDimension
#print axioms Atlas.Symplectic.square_one_minusDimension_even
#print axioms Atlas.Bilinear.determinantClass_orthogonal_decomposition
#print axioms Atlas.Bilinear.determinantClass_involution
#print axioms Atlas.Symplectic.negative_mul_square_one
#print axioms Atlas.Symplectic.negative_minus_eq_plus
#print axioms Atlas.Symplectic.minusDimension_neg_add
#print axioms Atlas.Symplectic.projection_square_one_isConj_iff
#print axioms Atlas.Symplectic.signRepresentative_empty
#print axioms Atlas.Symplectic.minusDimension_one
#print axioms Atlas.Symplectic.square_one_minusDimension_eq_zero_iff
#print axioms Atlas.Symplectic.square_one_minusDimension_bounds
#print axioms Atlas.Symplectic.rankSignRepresentative
#print axioms Atlas.Symplectic.rankSignRepresentative_square
#print axioms Atlas.Symplectic.rankSignRepresentative_minusDimension
#print axioms Atlas.Symplectic.projection_lift_types_not_isConj
#print axioms Atlas.Symplectic.rankSignRepresentative_not_central
#print axioms Atlas.Symplectic.projectiveInvolutionRepresentative
#print axioms Atlas.Symplectic.projectiveInvolutionRepresentative_order
#print axioms Atlas.Symplectic.projectiveInvolutionRepresentative_injective
#print axioms Atlas.Symplectic.projectiveInvolutionRepresentative_exhaustive
#print axioms Atlas.Symplectic.projectiveInvolutionClass
#print axioms Atlas.Symplectic.projectiveInvolutionClass_bijective
#print axioms Atlas.Symplectic.k2_psp
#print axioms Atlas.involutionClassOfRepresentative
#print axioms Atlas.involutionClassesEquivRepresentatives
#print axioms Atlas.k2_eq_card_representatives
#print axioms Atlas.Quadratic.coordinateSign
#print axioms Atlas.Quadratic.coordinateSign_apply
#print axioms Atlas.Quadratic.coordinateSign_involutive
#print axioms Atlas.Quadratic.coordinateSignIsometry
#print axioms Atlas.Quadratic.coordinateSignMinusEquiv
#print axioms Atlas.Quadratic.coordinateSign_finrank_minus
#print axioms Atlas.Quadratic.coordinateSignMinusIsometry
#print axioms Atlas.Quadratic.discriminantClass_isometry
#print axioms Atlas.Quadratic.discriminantClass_sum_squares
#print axioms Atlas.Quadratic.involutionPlusForm
#print axioms Atlas.Quadratic.involutionMinusForm
#print axioms Atlas.Quadratic.involutionPlusForm_nondegenerate
#print axioms Atlas.Quadratic.involutionMinusForm_nondegenerate
#print axioms Atlas.Quadratic.involution_wall_discriminantClass
#print axioms Atlas.Quadratic.isometry_associated
#print axioms Atlas.Quadratic.involution_discriminant_product
#print axioms Atlas.Quadratic.involution_decomposition_quadratic
#print axioms Atlas.Quadratic.involutionIsometryOfParts
#print axioms Atlas.Quadratic.involutionIsometryOfParts_intertwines
#print axioms Atlas.Quadratic.involution_conjugator_of_wallClass
#print axioms Atlas.Quadratic.conjugateIsometry
#print axioms Atlas.Quadratic.conjugateIsometry_involutive
#print axioms Atlas.Quadratic.conjugateMinusIsometry
#print axioms Atlas.Quadratic.conjugateIsometry_finrank_minus
#print axioms Atlas.Quadratic.finite_nondegenerate_normal_form
#print axioms Atlas.Quadratic.normalWeights_initial
#print axioms Atlas.Quadratic.exists_square_spinor_involution
#print axioms Atlas.Orthogonal.B_elementary_k2
#print axioms Atlas.Orthogonal.B_k2
#print axioms Atlas.Orthogonal.B_involution_data
#print axioms Atlas.Orthogonal.B_involution_half_minus_dimension
#print axioms Atlas.Orthogonal.B_involutions_isConj_of_minus_dimension
#print axioms Atlas.Orthogonal.B_involutions_minus_dimension_of_isConj
#print axioms Atlas.Orthogonal.exists_B_involution_of_half_minus_dim
#print axioms Atlas.Orthogonal.involution_conjugator_of_minus_dimension_spinor
#print axioms Atlas.Orthogonal.involution_intrinsic_kernel_conjugator
#print axioms Atlas.Comparisons.Classical.oddB_C_involution_counts
#print axioms Atlas.Comparisons.Classical.oddB_not_equiv_C
#print axioms Atlas.Comparisons.Classical.oddB_same_order_nonisomorphic_C
#print axioms Atlas.Orthogonal.evenB_singular_first_ne_zero
#print axioms Atlas.Orthogonal.evenB_singular_eq_of_first_eq
#print axioms Atlas.Orthogonal.evenB_elementary_singular_transport
#print axioms Atlas.Orthogonal.evenB_elementary_pretransitive
#print axioms Atlas.Orthogonal.evenB_projective_pretransitive
#print axioms Atlas.Orthogonal.evenB_roots_normal_generate
#print axioms Atlas.Orthogonal.evenSingularLift_ne_zero
#print axioms Atlas.Orthogonal.evenSingularLift_smul
#print axioms Atlas.Orthogonal.evenSingularPointOfVector
#print axioms Atlas.Orthogonal.evenSingularPointLift
#print axioms Atlas.Orthogonal.evenSingularPointLift_surjective
#print axioms Atlas.Orthogonal.evenSingularPointLift_injective
#print axioms Atlas.Orthogonal.evenSingularPointEquiv
#print axioms Atlas.Orthogonal.evenSingularLift_equivariant
#print axioms Atlas.Orthogonal.evenSingularPointLift_smul
#print axioms Atlas.Orthogonal.evenSingularPointActionHom
#print axioms Atlas.Orthogonal.evenB_full_faithful
#print axioms Atlas.Orthogonal.evenB_projective_faithful
#print axioms Atlas.Orthogonal.evenB_full_primitive
#print axioms Atlas.Orthogonal.evenB_elementary_primitive
#print axioms Atlas.Orthogonal.evenB_projective_primitive
#print axioms Atlas.Orthogonal.singular_line_kernel_scalar_of_triangle
#print axioms Atlas.Orthogonal.B1_projective_singular_faithful
#print axioms Atlas.Orthogonal.elementary_perpendicular_stabilizer_line_transport
#print axioms Atlas.Orthogonal.elementary_singular_line_transport_of_isometry
#print axioms Atlas.Orthogonal.elementaryB1_singular_line_transport
#print axioms Atlas.Orthogonal.elementaryB2_perpendicular_stabilizer_line_transport
#print axioms Atlas.Orthogonal.singularPoints_smul_eq_of_scaled_rep
#print axioms Atlas.Orthogonal.singular_stabilizerB2_perpendicular_transitive
#print axioms Atlas.Orthogonal.singularPointsB2_primitive
#print axioms Atlas.Orthogonal.singularPointsB_primitive_rank_two_up
#print axioms Atlas.Orthogonal.projectiveSingularB_primitive_rank_two_up
#print axioms Atlas.Orthogonal.singular_stabilizerB_perpendicular_transitive_rank_two_up
#print axioms Atlas.Orthogonal.root_normalClosure_eq_top_of_line_transport
#print axioms Atlas.Orthogonal.B_faithful_all_rank
#print axioms Atlas.Orthogonal.B_coordinate_roots_generate_all_rank
#print axioms Atlas.Orthogonal.B_elementary_singular_line_transport_all_rank
#print axioms Atlas.Orthogonal.B_elementary_transitive_all_rank
#print axioms Atlas.Orthogonal.B_transitive_all_rank
#print axioms Atlas.Orthogonal.B_elementary_primitive_all_char
#print axioms Atlas.Orthogonal.B_primitive_all_char
#print axioms Atlas.Orthogonal.B_roots_normal_generate_all_rank
#print axioms Atlas.TypeBGeometricConstruction
#print axioms Atlas.typeB_geometric_construction
#print axioms Atlas.typeB_prime_power_geometric
#print axioms Atlas.exists_typeB_geometric
#print axioms Atlas.Orthogonal.elementary_le_of_root_and_line_transport
#print axioms Atlas.Orthogonal.two_root_cross_transport
#print axioms Atlas.Orthogonal.rootSubgroup_le_of_basis
#print axioms Atlas.Orthogonal.coordinateRootSubgroup
#print axioms Atlas.Orthogonal.coordinateRoot_mem
#print axioms Atlas.Orthogonal.coordinateRootSubgroup_le_elementary
#print axioms Atlas.Orthogonal.rootSubgroup_le_coordinateRootSubgroup
#print axioms Atlas.Orthogonal.coordinate_siegel_mem_of_coefficient_vanishing
#print axioms Atlas.Orthogonal.coordinate_root_le_of_coefficient_vanishing
#print axioms Atlas.Orthogonal.coordinateBasisD
#print axioms Atlas.Orthogonal.coordinateBasisB
#print axioms Atlas.Orthogonal.coordinateRootSubgroupD
#print axioms Atlas.Orthogonal.coordinateRootSubgroupB
#print axioms Atlas.Orthogonal.coordinateRootSubgroupD_le_elementary
#print axioms Atlas.Orthogonal.coordinateRootSubgroupB_le_elementary
#print axioms Atlas.Orthogonal.rootD_e_le_coordinate
#print axioms Atlas.Orthogonal.rootD_f_le_coordinate
#print axioms Atlas.Orthogonal.rootB_e_le_coordinate
#print axioms Atlas.Orthogonal.rootB_f_le_coordinate
#print axioms Atlas.Orthogonal.root_line_transport_of_pairing
#print axioms Atlas.Orthogonal.subgroup_line_transport_of_pairing
#print axioms Atlas.Orthogonal.coordinate_frame_line_transport
#print axioms Atlas.Orthogonal.coordinateD_line_transport
#print axioms Atlas.Orthogonal.coordinateB_line_transport
#print axioms Atlas.Orthogonal.coordinateRootSubgroupD_eq_elementary
#print axioms Atlas.Orthogonal.coordinateRootSubgroupB_eq_elementary
#print axioms Atlas.Orthogonal.B1_conjugation_mem_coordinate
#print axioms Atlas.Orthogonal.coordinateRootSubgroupB_one_eq_elementary
#print axioms Atlas.Orthogonal.coordinateRootSubgroupB_eq_elementary_of_pos
#print axioms Atlas.Comparisons.Classical.Checks.b3_three_k2
#print axioms Atlas.Comparisons.Classical.Checks.c3_three_k2
#print axioms Atlas.Comparisons.Classical.Checks.b3_three_not_equiv_c3
#print axioms Atlas.Comparisons.Classical.Checks.b3_three_same_order_c3
#print axioms Atlas.Orthogonal.Checks.b3_two_order
#print axioms Atlas.Orthogonal.Checks.b3_three_order
#print axioms Atlas.Orthogonal.Checks.b3_four_order
#print axioms Atlas.Orthogonal.B_sign_factor_eq_gcd
#print axioms Atlas.Orthogonal.B_full_order_gcd
#print axioms Atlas.Orthogonal.B_elementary_index_gcd_square
#print axioms Atlas.Orthogonal.Checks.b3_two_simple
#print axioms Atlas.Orthogonal.Checks.b3_three_simple
#print axioms Atlas.Orthogonal.Checks.b3_four_simple
#print axioms Atlas.Orthogonal.Checks.d4_two_simple
#print axioms Atlas.Orthogonal.Checks.d4_three_center_order
#print axioms Atlas.Orthogonal.Checks.b3_two_polar_radical
#print axioms Atlas.Orthogonal.Checks.b3_two_radical_vector_norm
#print axioms Atlas.Orthogonal.Checks.b3_two_quadratic_radical
#print axioms Atlas.Orthogonal.Checks.d4_two_dickson_exchange
#print axioms Atlas.Orthogonal.Checks.d4_two_dickson_surjective
#print axioms Atlas.Orthogonal.Checks.d4_two_dickson_kernel
#print axioms Atlas.fieldEquivSL
#print axioms Atlas.fieldEquivPSL
#print axioms Atlas.fieldEquivPSL_projection
#print axioms Atlas.Comparisons.Exceptional.cardFourFieldEquiv
#print axioms Atlas.Comparisons.Exceptional.psl2Card4EquivAlt5
#print axioms Atlas.Comparisons.Exceptional.psl2Card4EquivAlt5_action
#print axioms Atlas.Comparisons.Exceptional.psl2FourEquivAlt5
#print axioms Atlas.Comparisons.Exceptional.psl2Card5EquivAlt5
#print axioms Atlas.Comparisons.Exceptional.psl2FiveEquivAlt5
#print axioms Atlas.Comparisons.Exceptional.psl2Card4RecognitionEquivAlt5
#print axioms Atlas.Comparisons.Exceptional.psl2Card4EquivPsl2Five
#print axioms Atlas.Comparisons.Exceptional.psl2FourEquivPsl2Five
#print axioms Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two
#print axioms Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two
#print axioms Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two_action
#print axioms Atlas.GroupTheory.smallSimpleOrder60EquivAlt5
#print axioms Atlas.GroupTheory.not_mulEquiv_of_sylow_center_card_ne
#print axioms Atlas.Comparisons.Exceptional.DeletedEight.quotient_finrank
#print axioms Atlas.Comparisons.Exceptional.DeletedEight.splitIsometry
#print axioms Atlas.Comparisons.Exceptional.DeletedEight.permutationHom_injective
#print axioms Atlas.Comparisons.Exceptional.alt8EquivD3Two
#print axioms Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
#print axioms Atlas.Comparisons.Exceptional.DeletedEight.quotient_polar_nondegenerate
#print axioms Atlas.LinearGroups.UnitriangularThree.sylowTwo
#print axioms Atlas.LinearGroups.UnitriangularThree.sylowTwo_center_card
#print axioms Atlas.LinearGroups.UnitriangularFour.sylowTwo
#print axioms Atlas.LinearGroups.UnitriangularFour.sylowTwo_center_card
#print axioms Atlas.Comparisons.Exceptional.psl4Two_not_equiv_psl3Card4
#print axioms Atlas.Comparisons.Exceptional.alt8_not_equiv_psl3Card4
#print axioms Atlas.Comparisons.Exceptional.psl4Two_card_eq_psl3Card4
#print axioms Atlas.Comparisons.Exceptional.alt8_card_eq_psl3Card4
#print axioms Atlas.GroupTheory.commutatorEquiv
#print axioms Atlas.GroupTheory.commutatorEquiv_coe
#print axioms Atlas.Comparisons.Exceptional.b2BinaryDerivedEquivC2Derived
#print axioms Atlas.Comparisons.Exceptional.c2BinaryDerivedEquivAlt6
#print axioms Atlas.Comparisons.Exceptional.b2BinaryDerivedEquivC2Derived_coe
#print axioms Atlas.Comparisons.Exceptional.c2BinaryDerivedEquivAlt6_coherence
#print axioms Atlas.Comparisons.Exceptional.Nine.card
#print axioms Atlas.Comparisons.Exceptional.Nine.fieldEquiv
#print axioms Atlas.Comparisons.Exceptional.Nine.upper_coordinates
#print axioms Atlas.Comparisons.Exceptional.Nine.lower_coordinates
#print axioms Atlas.Comparisons.Exceptional.Nine.sl_generated
#print axioms Atlas.Comparisons.Exceptional.Nine.psl_generated
#print axioms Atlas.Comparisons.Exceptional.Nine.marking
#print axioms Atlas.Comparisons.Exceptional.Nine.permutation
#print axioms Atlas.Comparisons.Exceptional.Nine.permutation_injective
#print axioms Atlas.Comparisons.Exceptional.Nine.permutation_upper
#print axioms Atlas.Comparisons.Exceptional.Nine.permutation_omega
#print axioms Atlas.Comparisons.Exceptional.Nine.permutation_inversion
#print axioms Atlas.Comparisons.Exceptional.TriplePartitions.partition_card
#print axioms Atlas.Comparisons.Exceptional.TriplePartitions.marking
#print axioms Atlas.Comparisons.Exceptional.TriplePartitions.action
#print axioms Atlas.Comparisons.Exceptional.TriplePartitions.action_injective
#print axioms Atlas.Comparisons.Exceptional.TriplePartitions.action_firstCycle
#print axioms Atlas.Comparisons.Exceptional.TriplePartitions.action_secondCycle
#print axioms Atlas.Comparisons.Exceptional.TriplePartitions.action_doubleSwap
#print axioms Atlas.Comparisons.Exceptional.psl2Card9_card
#print axioms Atlas.Comparisons.Exceptional.alt6_card
#print axioms Atlas.Comparisons.Exceptional.psl2NineCoordinatesEquivAlt6
#print axioms Atlas.Comparisons.Exceptional.psl2NineCoordinatesEquivAlt6_action
#print axioms Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6
#print axioms Atlas.Comparisons.Exceptional.psl2NineEquivAlt6
#print axioms Atlas.Comparisons.Exceptional.psl2Card9EquivB2BinaryDerived
#print axioms Atlas.Comparisons.Exceptional.psl2Card9EquivC2BinaryDerived
#print axioms Atlas.SplitOctonion.mul
#print axioms Atlas.SplitOctonion.unit
#print axioms Atlas.SplitOctonion.trace
#print axioms Atlas.SplitOctonion.norm
#print axioms Atlas.SplitOctonion.conjugate
#print axioms Atlas.SplitOctonion.multiplication
#print axioms Atlas.SplitOctonion.unit_mul
#print axioms Atlas.SplitOctonion.mul_unit
#print axioms Atlas.SplitOctonion.quadratic_identity
#print axioms Atlas.SplitOctonion.mul_conjugate
#print axioms Atlas.SplitOctonion.conjugate_mul
#print axioms Atlas.SplitOctonion.norm_mul
#print axioms Atlas.SplitOctonion.conjugate_mul_reverse
#print axioms Atlas.SplitOctonion.map_mul_of_basis
#print axioms Atlas.SplitOctonion.linearMap_ext
#print axioms Atlas.Algebra.MultiplicativeLinearAut.map_unit
#print axioms Atlas.Algebra.MultiplicativeLinearAut.representation
#print axioms Atlas.Algebra.MultiplicativeLinearAut.representation_injective
#print axioms Atlas.SplitOctonion.automorphism_unit
#print axioms Atlas.SplitOctonion.automorphism_trace_norm
#print axioms Atlas.SplitOctonion.automorphism_trace
#print axioms Atlas.SplitOctonion.automorphism_norm
#print axioms Atlas.SplitOctonion.automorphism_conjugate
#print axioms Atlas.G2.Model
#print axioms Atlas.G2.representation_injective
#print axioms Atlas.G2.carrier_finrank
#print axioms Atlas.G2.fieldEquiv
#print axioms Atlas.G2.fieldEquiv_action
#print axioms Atlas.G2.rootA
#print axioms Atlas.G2.rootA_add
#print axioms Atlas.G2.rootA_injective
#print axioms Atlas.G2.rootB
#print axioms Atlas.G2.rootB_add
#print axioms Atlas.G2.rootB_injective
#print axioms Atlas.G2.rootC
#print axioms Atlas.G2.rootC_add
#print axioms Atlas.G2.rootC_injective
#print axioms Atlas.G2.rootD
#print axioms Atlas.G2.rootD_add
#print axioms Atlas.G2.rootD_injective
#print axioms Atlas.G2.rootE
#print axioms Atlas.G2.rootE_add
#print axioms Atlas.G2.rootE_injective
#print axioms Atlas.G2.rootF
#print axioms Atlas.G2.rootF_add
#print axioms Atlas.G2.rootF_injective
#print axioms Atlas.G2.exists_mul_ne_mul
#print axioms Atlas.G2.weylR
#print axioms Atlas.G2.weylS
#print axioms Atlas.G2.weylR_sq
#print axioms Atlas.G2.weylS_sq
#print axioms Atlas.G2.torus
#print axioms Atlas.G2.torusHom
#print axioms Atlas.G2.torusHom_injective
#print axioms Atlas.G2.torusParameterEquiv
#print axioms Atlas.G2.card_splitTorus
#print axioms Atlas.G2.torus_rootA
#print axioms Atlas.G2.torus_rootB
#print axioms Atlas.G2.torus_rootC
#print axioms Atlas.G2.torus_rootD
#print axioms Atlas.G2.torus_rootE
#print axioms Atlas.G2.torus_rootF
#print axioms Atlas.G2.torus_unipotentProduct
#print axioms Atlas.G2.unipotentProduct
#print axioms Atlas.G2.unipotentParameters_product
#print axioms Atlas.G2.unipotentProduct_mul
#print axioms Atlas.G2.unipotentProduct_inv
#print axioms Atlas.G2.unipotent_eq_range
#print axioms Atlas.G2.unipotentEquiv
#print axioms Atlas.G2.card_unipotent
#print axioms Atlas.G2.unipotent_disjoint_torus
#print axioms Atlas.G2.torus_normalizes_unipotent
#print axioms Atlas.G2.borelProductEquiv
#print axioms Atlas.G2.card_borel
#print axioms Atlas.G2.singularOctonionsEquivCoordinates
#print axioms Atlas.G2.nonzeroSingularOctonionsEquivCoordinates
#print axioms Atlas.G2.card_nonzeroSingularOctonions
#print axioms Atlas.G2.SingularPoints
#print axioms Atlas.G2.singularPointMk
#print axioms Atlas.G2.nonzeroSingularEquivPointsUnits
#print axioms Atlas.G2.card_singularPoints
#print axioms Atlas.G2.card_singularPoints_sum
#print axioms Atlas.G2.singularPointsAction
#print axioms Atlas.G2.singular_lines_kernel_trivial
#print axioms Atlas.G2.singularPointsFaithful
#print axioms Atlas.G2.singular_vector_reduction_first
#print axioms Atlas.G2.PairStabilizer.fixingPair
#print axioms Atlas.G2.PairStabilizer.fixingPairEquivSL2
#print axioms Atlas.G2.fixingFirstVector
#print axioms Atlas.G2.fixingFirstVectorEquivPartners
#print axioms Atlas.G2.card_fixingFirstVector_SL2
#print axioms Atlas.G2.firstPoint
#print axioms Atlas.G2.pointStabilizer
#print axioms Atlas.G2.pointStabilizerEquiv
#print axioms Atlas.G2.lineScalarHom
#print axioms Atlas.G2.lineScalarHom_surjective
#print axioms Atlas.G2.lineScalarHom_kernel
#print axioms Atlas.G2.exists_smul_firstPoint
#print axioms Atlas.G2.singularPoints_pretransitive
#print axioms Atlas.G2.generated
#print axioms Atlas.G2.generated_eq_top
#print axioms Atlas.G2.parabolic
#print axioms Atlas.G2.parabolic_eq_pointStabilizer
#print axioms Atlas.G2.parabolicNormalForm
#print axioms Atlas.G2.card_parabolic
#print axioms Atlas.G2.borel_relIndex_parabolic
#print axioms Atlas.G2.card_Model_eq_points_mul_stabilizer
#print axioms Atlas.G2.card_Model
#print axioms Atlas.G2.card_pointStabilizer_formula
#print axioms Atlas.G2.card_fixingFirstVector_formula
#print axioms Atlas.G2.OrderChecks.binary_order
#print axioms Atlas.G2.OrderChecks.ternary_order
#print axioms Atlas.G2.OrderChecks.four_order
#print axioms Atlas.G2.OrderChecks.five_order
#print axioms Atlas.G2.OrderChecks.eight_order
#print axioms Atlas.G2.OrderChecks.binary_points
#print axioms Atlas.G2.OrderChecks.ternary_points
#print axioms Atlas.G2.OrderChecks.four_points
#print axioms Atlas.G2.parabolic_four_point_representatives
#print axioms Atlas.G2.parabolic_orbitPoint_distinct
#print axioms Atlas.G2.card_polarSingularPoints
#print axioms Atlas.G2.card_lowerSingularPoints
#print axioms Atlas.G2.orbitClass
#print axioms Atlas.G2.orbitClass_eq_iff
#print axioms Atlas.G2.orbitClass_zero_iff
#print axioms Atlas.G2.orbitClass_le_one_iff
#print axioms Atlas.G2.orbitClass_le_two_iff
#print axioms Atlas.G2.card_orbitClass_zero
#print axioms Atlas.G2.card_orbitClass_one
#print axioms Atlas.G2.card_orbitClass_two
#print axioms Atlas.G2.card_orbitClass_three
#print axioms Atlas.G2.distinguishedPlane
#print axioms Atlas.G2.distinguishedPlane_product_span
#print axioms Atlas.G2.plane_preserver_mem_pointStabilizer
#print axioms Atlas.G2.planePoints
#print axioms Atlas.G2.planePoints_stabilizer_le
#print axioms Atlas.G2.planePoints_not_block
#print axioms Atlas.G2.singularSubdegree
#print axioms Atlas.G2.subdegree_block_index_candidates
#print axioms Atlas.G2.card_orbitClass
#print axioms Atlas.G2.singularPoints_primitive
#print axioms Atlas.G2.longRootLocal
#print axioms Atlas.G2.longRootParameterEquiv
#print axioms Atlas.G2.card_longRootLocal
#print axioms Atlas.G2.longRootLocal_commutative
#print axioms Atlas.G2.longRootNormalClosure
#print axioms Atlas.G2.unipotent_le_longRootNormalClosure
#print axioms Atlas.G2.normal_eq_top_of_unipotent
#print axioms Atlas.G2.longRootNormalClosure_eq_top
#print axioms Atlas.G2.pointStabilizer_le_longRootNormalizer
#print axioms Atlas.G2.longRootLocal_normal_in_pointStabilizer
#print axioms Atlas.G2.rootA_mem_commutator
#print axioms Atlas.G2.isPerfect
#print axioms Atlas.G2.localAt
#print axioms Atlas.G2.conjugate_local_eq
#print axioms Atlas.G2.localAt_eq_of_transport
#print axioms Atlas.G2.localAt_first
#print axioms Atlas.G2.localAt_conj
#print axioms Atlas.G2.localAt_commutative
#print axioms Atlas.G2.localAtEquiv
#print axioms Atlas.G2.card_localAt
#print axioms Atlas.G2.localAt_iSup_eq_normalClosure
#print axioms Atlas.G2.iwasawa
#print axioms Atlas.G2.isSimple
#print axioms Atlas.G2.SimplicityChecks.ternary_simple
#print axioms Atlas.G2.SimplicityChecks.four_simple
#print axioms Atlas.G2.SimplicityChecks.five_simple
#print axioms Atlas.G2.SimplicityChecks.eight_simple
#print axioms Atlas.G2.SimplicityChecks.binary_noncommutative
#print axioms Atlas.G2.SimplicityChecks.ternary_noncommutative
#print axioms Atlas.G2.Binary.card_Line
#print axioms Atlas.G2.Binary.card_fixed_rootA
#print axioms Atlas.G2.Binary.card_fixed_rootF
#print axioms Atlas.G2.BinaryException.lineSign_kernel
#print axioms Atlas.G2.card_longRootNormalClosure_binary
#print axioms Atlas.G2.index_longRootNormalClosure_binary
#print axioms Atlas.G2.not_simple_binary
#print axioms Atlas.G2.isSimple_iff
#print axioms Atlas.G2.rootA_one_ne_one
#print axioms Atlas.G2.localAt_normal
#print axioms Atlas.typeG2_construction
#print axioms Atlas.typeG2_prime_power
#print axioms Atlas.exists_typeG2
#print axioms Atlas.exists_typeG2_prime_power

#print axioms Atlas.ReeG2.order
#print axioms Atlas.ReeG2.simple
#print axioms Atlas.ReeG2.perfect
#print axioms Atlas.ReeG2.fieldEquiv
#print axioms Atlas.ReeG2.g2Embedding_injective
#print axioms Atlas.typeReeG2_construction
#print axioms Atlas.exists_typeReeG2
#print axioms Atlas.exists_typeReeG2_parameter

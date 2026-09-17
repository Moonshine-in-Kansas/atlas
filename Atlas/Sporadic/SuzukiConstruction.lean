import Atlas.Sporadic.SuzukiStructure
import Atlas.Lattices.LeechConstruction

noncomputable section
namespace Atlas.Sporadic.Suzuki
open Atlas.Algebra Atlas.Codes Atlas.Lattices Atlas.Conway MulAction

/-- Construction certificate for the actual scalar quotient of the retained
Leech centralizer. The linear group and its sign quotient remain distinct models. -/
structure CompleteConstruction : Prop where
  leech : LeechConstruction
  integral_rank : Module.finrank ℤ Lattice=24
  integral_free : Module.Free ℤ Lattice
  integral_finite : Module.Finite ℤ Lattice
  scalar_rank : Module.finrank Scalar Lattice=12
  scalar_finite : Module.Finite Scalar Lattice
  rational_scalar_rank : Module.finrank ScalarField Coordinates=12
  lattice_onto : ∀ z : Coordinates,
    z ∈ rationalEisensteinLattice ↔ latticeComparison z ∈ rationalLeech
  lattice_isometry : ∀ z w : Coordinates,
    rationalForm (latticeComparison z) (latticeComparison w)=eisensteinBilinear z w
  theta_quotient_card : Nat.card (eisensteinLeechModule ⧸ eisensteinThetaEnd.range)=3^12
  rotation_order : orderOf scalarRotation=3
  rotation_fixed_iff : ∀ x : Atlas.Lattices.leech,scalarRotation.val x=x ↔ x=0
  rotation_polynomial : ∀ x : Atlas.Lattices.leech,
    scalarRotation.val (scalarRotation.val x)+scalarRotation.val x+x=0
  full_centralizer : eisensteinHermitianToCo0.range=eisensteinCentralizer
  linear_comparison : Nonempty (HermitianGroup ≃* LinearCover)
  linear_compatible : ∀ g : HermitianGroup,∀ z : Coordinates,
    (fullIsometryEquiv (embedding (linearComparison g))).val (latticeComparison z)=
      latticeComparison (linearRepresentation g z)
  linear_faithful : Function.Injective linearRepresentation
  cover_embedding : Function.Injective embedding
  scalar_center : Subgroup.center LinearCover=eisensteinCentralizerScalars
  center_card : Nat.card (Subgroup.center LinearCover)=6
  linear_card : Nat.card LinearCover=2690072985600
  finite : Finite Model
  card : Nat.card Model=448345497600
  order : Nat.card Model=2^13*3^7*5^2*7*11*13
  simple : IsSimpleGroup Model
  noncommuting : ∃ g h : Model,g*h≠h*g
  perfect : Group.IsPerfect Model
  degree : Nat.card Frames=232960
  faithful : FaithfulSMul Model Frames
  primitive : IsPreprimitive Model Frames
  full_frame_stabilizer : stabilizer HermitianGroup baseFrame=eisensteinCoordinateFrameStabilizer
  frame_stabilizer_card : Nat.card FrameStabilizer=11547360
  frame_stabilizer_maximal : IsCoatom eisensteinCoordinateFrameStabilizer
  local_comparison : Nonempty (FrameStabilizer ⧸ eisensteinFrameScalarSubgroup ≃* LocalModel)
  local_card : Nat.card LocalModel=1924560
  mathieu_comparison : Nonempty (TernaryMathieu11 ≃* TernaryPureAutomorphism)
  suborbit_card : ∀ i : Fin 13,Nat.card (suborbit i)=subdegree i
  suborbit_cover : ∀ F : Frames,∃ i : Fin 13,F ∈ suborbit i
  local_embedding_range : localEmbedding.range=stabilizer Model baseFrame
  local_orbits : ∀ F : Frames,orbit (stabilizer Model baseFrame) F=orbit FrameStabilizer F
  suborbit_pairwise : Pairwise (fun i j => Disjoint (suborbit i) (suborbit j))
  suborbit_orbits : ∀ i : Fin 13,∃ F : Frames,suborbit i=orbit FrameStabilizer F
  phase_normal_generation : Subgroup.normalClosure (eisensteinProjectivePhases : Set Model)=⊤
  phase_fourier_fusion :
    eisensteinProjectiveProjection eisensteinFourierIsometry *
      eisensteinLocalProjectiveEmbedding eisensteinProjectiveFusionInput *
        (eisensteinProjectiveProjection eisensteinFourierIsometry)⁻¹ =
      eisensteinLocalProjectiveEmbedding eisensteinProjectiveFusionOutput
  linear_frame_kernel : (toPermHom HermitianGroup Frames).ker=eisensteinScalarSubgroup
  monomial_fourier_generation : eisensteinGeneratedGroup=⊤
  quotient_surjective : Function.Surjective projection
  triple_card : Nat.card TripleModel=1345036492800
  triple_co1_injective : Function.Injective tripleToConway1
  triple_co1_compatible : ∀ g : LinearCover,
    tripleToConway1 (QuotientGroup.mk g)=leechCentralProjection (embedding g)
  triple_projection_surjective : Function.Surjective tripleProjection
  triple_kernel_card : Nat.card tripleProjection.ker=3
  triple_kernel_central : tripleProjection.ker ≤ Subgroup.center TripleModel

theorem construction : CompleteConstruction where
  leech := leech_constructed
  integral_rank := integral_rank
  integral_free := integral_free
  integral_finite := integral_finite
  scalar_rank := scalar_rank
  scalar_finite := scalar_finite
  rational_scalar_rank := rational_scalar_rank
  lattice_onto := lattice_comparison_onto
  lattice_isometry := lattice_comparison_isometry
  theta_quotient_card := theta_quotient_card
  rotation_order := rotation_order
  rotation_fixed_iff := rotation_fixed_iff
  rotation_polynomial := rotation_polynomial
  full_centralizer := full_centralizer
  linear_comparison := ⟨linearComparison⟩
  linear_compatible := linear_comparison_compatible
  linear_faithful := linear_faithful
  cover_embedding := embedding_injective
  scalar_center := center
  center_card := center_card
  linear_card := linear_card
  finite := finite
  card := card
  order := order
  simple := isSimpleGroup
  noncommuting := exists_mul_ne_mul
  perfect := perfect
  degree := degree
  faithful := faithful
  primitive := primitive
  full_frame_stabilizer := full_frame_stabilizer
  frame_stabilizer_card := frame_stabilizer_card
  frame_stabilizer_maximal := frame_stabilizer_maximal
  local_comparison := ⟨localComparison⟩
  local_card := local_card
  mathieu_comparison := ⟨mathieuComparison⟩
  suborbit_card := suborbit_card
  suborbit_cover := suborbit_cover
  local_embedding_range := localEmbedding_range
  local_orbits := local_orbit_correspondence
  suborbit_pairwise := suborbit_pairwise
  suborbit_orbits := suborbit_is_orbit
  phase_normal_generation := phase_normal_generation
  phase_fourier_fusion := phase_fourier_fusion
  linear_frame_kernel := linear_frame_kernel
  monomial_fourier_generation := monomial_fourier_generation
  quotient_surjective := projection_surjective
  triple_card := triple_card
  triple_co1_injective := tripleToConway1_injective
  triple_co1_compatible := tripleToConway1_compatible
  triple_projection_surjective := tripleProjection_surjective
  triple_kernel_card := tripleProjection_kernel_card
  triple_kernel_central := tripleProjection_kernel_central

theorem construction_complete : CompleteConstruction := construction

theorem exists_model : ∃ (G : Type) (_ : Group G),Nonempty (G ≃* Model) ∧
    Finite G ∧ Nat.card G=448345497600 ∧ IsSimpleGroup G ∧
    (∃ g h : G,g*h≠h*g) ∧ CompleteConstruction :=
  ⟨Model,inferInstance,⟨MulEquiv.refl _⟩,finite,card,isSimpleGroup,exists_mul_ne_mul,construction⟩

end Atlas.Sporadic.Suzuki

import Atlas.Sporadic.Suzuki
import Atlas.Lattices.EisensteinScalarRank
import Atlas.Lattices.EisensteinOrthogonality
import Atlas.Conway.EisensteinMaximalStabilizers

noncomputable section
namespace Atlas.Sporadic.Suzuki
open Atlas.Algebra Atlas.Codes Atlas.Lattices Atlas.Conway MulAction

abbrev Scalar := Eisenstein
abbrev ScalarField := EisensteinRational
abbrev Coordinates := EisensteinRationalCoordinates
abbrev FrameStabilizer := eisensteinCoordinateFrameStabilizer
abbrev LocalModel := TernaryLocalPhaseGroup

def latticeComparison : Coordinates ≃ₗ[ℚ] RationalCoordinates := eisensteinComparison

def scalarRotation : LeechIsometryGroup := eisensteinRho

def hermitianForm : Coordinates → Coordinates → ScalarField := eisensteinHermitian

def linearRepresentation : HermitianGroup →*
    (Coordinates ≃ₗ[ℚ] Coordinates) := eisensteinHermitianGroup.subtype

def frameGroupComparison : EisensteinFrameAbstractGroup ≃* FrameStabilizer :=
  eisensteinFullFrameGroupEquiv

def localComparison : FrameStabilizer ⧸ eisensteinFrameScalarSubgroup ≃* LocalModel :=
  eisensteinFrameModuloScalarsEquiv

def localEmbedding : LocalModel →* Model := eisensteinLocalProjectiveEmbedding

def mathieuComparison : TernaryMathieu11 ≃* TernaryPureAutomorphism := ternaryPureMathieu11Equiv

def suborbit (i : Fin 13) : Set Frames := eisensteinSuborbitFrames i

def subdegree (i : Fin 13) : ℕ := eisensteinSubdegree i

theorem lattice_comparison_onto (z : Coordinates) :
    z ∈ rationalEisensteinLattice ↔ latticeComparison z ∈ rationalLeech :=
  eisensteinComparison_lattice_iff z

theorem lattice_comparison_isometry (z w : Coordinates) :
    rationalForm (latticeComparison z) (latticeComparison w)=eisensteinBilinear z w :=
  eisensteinComparison_isometry z w

theorem integral_rank : Module.finrank ℤ Lattice=24 := eisensteinLeech_rank

theorem scalar_rank : Module.finrank Scalar Lattice=12 := eisensteinLeech_scalar_rank

theorem rational_scalar_rank : Module.finrank ScalarField Coordinates=12 :=
  eisensteinRationalCoordinates_scalar_finrank

theorem scalar_finite : Module.Finite Scalar Lattice := inferInstance

theorem integral_free : Module.Free ℤ Lattice := inferInstance

theorem integral_finite : Module.Finite ℤ Lattice := inferInstance

theorem rotation_order : orderOf scalarRotation=3 := eisensteinRho_order

theorem rotation_fixed_iff (x : leech) : scalarRotation.val x=x ↔ x=0 := eisensteinRho_fixed_iff x

theorem rotation_polynomial (x : leech) :
    scalarRotation.val (scalarRotation.val x)+scalarRotation.val x+x=0 := eisensteinRho_polynomial x

theorem full_centralizer : eisensteinHermitianToCo0.range=eisensteinCentralizer :=
  eisensteinHermitianToCo0_range

theorem linear_comparison_compatible (g : HermitianGroup) (z : Coordinates) :
    (fullIsometryEquiv (embedding (linearComparison g))).val (latticeComparison z)=
      latticeComparison (linearRepresentation g z) := eisensteinCentralizerEquiv_agrees g z

theorem linear_faithful : Function.Injective linearRepresentation := Subtype.val_injective

theorem linear_scalar_linear (g : HermitianGroup) (a : ScalarField) (z : Coordinates) :
    linearRepresentation g (a • z)=a • linearRepresentation g z := g.property.1 a z

theorem linear_hermitian (g : HermitianGroup) (z w : Coordinates) :
    hermitianForm (linearRepresentation g z) (linearRepresentation g w)=hermitianForm z w :=
  g.property.2.1 z w

theorem linear_lattice (g : HermitianGroup) (z : Coordinates) :
    z ∈ rationalEisensteinLattice ↔ linearRepresentation g z ∈ rationalEisensteinLattice :=
  g.property.2.2 z

theorem degree : Nat.card Frames=232960 := eisensteinFrame_card

theorem faithful : FaithfulSMul Model Frames := inferInstance

theorem primitive : IsPreprimitive Model Frames := eisensteinProjective_frame_primitive

theorem transitive : IsPretransitive Model Frames := by
  letI := primitive
  infer_instance

theorem full_frame_stabilizer : stabilizer HermitianGroup baseFrame=eisensteinCoordinateFrameStabilizer :=
  eisensteinStandardFrame_stabilizer

theorem frame_stabilizer_card : Nat.card FrameStabilizer=11547360 := eisensteinFullFrameStabilizer_order

theorem frame_stabilizer_maximal : IsCoatom eisensteinCoordinateFrameStabilizer := by
  letI := eisensteinHermitian_frame_primitive
  exact eisensteinFullStabilizer_maximal_of_primitive

theorem local_card : Nat.card LocalModel=1924560 := ternaryLocalPhaseGroup_order

theorem suborbit_card (i : Fin 13) : Nat.card (suborbit i)=subdegree i :=
  eisensteinSuborbitFrames_card i

theorem suborbit_cover (F : Frames) : ∃ i : Fin 13,F ∈ suborbit i :=
  eisensteinSuborbitFrames_cover F

theorem suborbit_disjoint : Pairwise (fun i j => Disjoint (suborbit i) (suborbit j)) :=
  eisensteinSuborbitFrames_pairwise

theorem suborbit_pairwise : Pairwise (fun i j => Disjoint (suborbit i) (suborbit j)) :=
  suborbit_disjoint

theorem localEmbedding_range : localEmbedding.range=stabilizer Model baseFrame :=
  eisensteinLocalProjectiveEmbedding_range

theorem local_orbit_correspondence (F : Frames) :
    orbit (stabilizer Model baseFrame) F=orbit FrameStabilizer F :=
  eisensteinProjectiveStabilizer_orbit F

theorem suborbit_transitive (i : Fin 13) (F H : Frames)
    (hF : F ∈ suborbit i) (hH : H ∈ suborbit i) :
    ∃ g : FrameStabilizer,g.val • F=H := eisensteinSuborbitFrames_transitive i F H hF hH

theorem suborbit_is_orbit (i : Fin 13) :
    ∃ F : Frames,suborbit i=orbit FrameStabilizer F := eisensteinSuborbitFrames_orbit i

theorem phase_normal_generation :
    Subgroup.normalClosure (eisensteinProjectivePhases : Set Model)=⊤ := eisensteinPhase_normalClosure

theorem linear_frame_kernel : (toPermHom HermitianGroup Frames).ker=eisensteinScalarSubgroup :=
  eisensteinHermitianFrame_kernel

theorem monomial_fourier_generation : eisensteinGeneratedGroup=⊤ := eisensteinGeneratedGroup_eq_top

theorem phase_fourier_fusion :
    eisensteinProjectiveProjection eisensteinFourierIsometry *
      eisensteinLocalProjectiveEmbedding eisensteinProjectiveFusionInput *
        (eisensteinProjectiveProjection eisensteinFourierIsometry)⁻¹ =
      eisensteinLocalProjectiveEmbedding eisensteinProjectiveFusionOutput :=
  eisensteinProjective_fusion

theorem theta_quotient_card :
    Nat.card (eisensteinLeechModule ⧸ eisensteinThetaEnd.range)=3^12 :=
  eisensteinTheta_quotient_card

end Atlas.Sporadic.Suzuki

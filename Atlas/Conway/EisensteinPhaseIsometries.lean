import Atlas.Conway.EisensteinCentralizer
import Atlas.Lattices.EisensteinPhases
import Atlas.Codes.TernaryGolayQuotient

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

/-- The same integral phases embedded in the rational scalar field. -/
def eisensteinRationalDiagonal (t : TernaryWord)
    (z : EisensteinRationalCoordinates) : EisensteinRationalCoordinates :=
  fun i => eisensteinToRational (eisensteinPhase (t i)) * z i

@[simp] theorem eisensteinRationalDiagonal_zero (z : EisensteinRationalCoordinates) :
    eisensteinRationalDiagonal 0 z = z := by
  funext i; simp [eisensteinRationalDiagonal]

theorem eisensteinRationalDiagonal_add (s t : TernaryWord)
    (z : EisensteinRationalCoordinates) :
    eisensteinRationalDiagonal (s+t) z =
      eisensteinRationalDiagonal s (eisensteinRationalDiagonal t z) := by
  funext i; simp [eisensteinRationalDiagonal, eisensteinPhase_add, mul_assoc]

def eisensteinRationalDiagonalEquiv (t : TernaryWord) :
    EisensteinRationalCoordinates ≃ₗ[ℚ] EisensteinRationalCoordinates where
  toFun := eisensteinRationalDiagonal t
  invFun := eisensteinRationalDiagonal (-t)
  left_inv z := by
    rw [← eisensteinRationalDiagonal_add, neg_add_cancel, eisensteinRationalDiagonal_zero]
  right_inv z := by
    rw [← eisensteinRationalDiagonal_add, add_neg_cancel, eisensteinRationalDiagonal_zero]
  map_add' z w := by funext i; simp [eisensteinRationalDiagonal, mul_add]
  map_smul' a z := by funext i; simp [eisensteinRationalDiagonal]

theorem eisensteinRationalDiagonal_embedding (t : TernaryWord) (z : EisensteinCoordinates) :
    eisensteinRationalDiagonal t (eisensteinCoordinateEmbedding z) =
      eisensteinCoordinateEmbedding (eisensteinDiagonal t z) := by
  funext i
  exact (map_mul eisensteinToRational _ _).symm

theorem eisensteinRationalDiagonal_lattice_iff (t : ternaryGolay)
    (z : EisensteinRationalCoordinates) :
    z ∈ rationalEisensteinLattice ↔ eisensteinRationalDiagonal t.val z ∈ rationalEisensteinLattice := by
  have hf (s : ternaryGolay) {w : EisensteinRationalCoordinates}
      (hw : w ∈ rationalEisensteinLattice) :
      eisensteinRationalDiagonal s.val w ∈ rationalEisensteinLattice := by
    obtain ⟨v, hv, rfl⟩ := hw
    rw [eisensteinRationalDiagonal_embedding]
    exact ⟨_, eisensteinDiagonal_mem s hv, rfl⟩
  constructor
  · exact hf t
  · intro hz
    have h := hf (-t) hz
    rw [← eisensteinRationalDiagonal_add] at h
    change eisensteinRationalDiagonal (-t.val+t.val) z ∈ rationalEisensteinLattice at h
    simpa only [neg_add_cancel, eisensteinRationalDiagonal_zero] using h

theorem eisensteinRationalPhase_norm (a : ZMod 3) :
    star (eisensteinToRational (eisensteinPhase a)) *
      eisensteinToRational (eisensteinPhase a) = 1 := by
  revert a; decide +kernel

theorem eisensteinRationalDiagonal_hermitian (t : TernaryWord)
    (z w : EisensteinRationalCoordinates) :
    eisensteinHermitian (eisensteinRationalDiagonal t z) (eisensteinRationalDiagonal t w) =
      eisensteinHermitian z w := by
  unfold eisensteinHermitian eisensteinRationalDiagonal
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [star_mul]
  calc
    _ = (star (eisensteinToRational (eisensteinPhase (t i))) *
        eisensteinToRational (eisensteinPhase (t i))) * (star (z i) * w i) := by ring
    _ = _ := by rw [eisensteinRationalPhase_norm, one_mul]

/-- The code acts by full Hermitian isometries of the actual scalar lattice. -/
def eisensteinPhaseIsometries : Multiplicative ternaryGolay →* eisensteinHermitianGroup where
  toFun t := ⟨eisensteinRationalDiagonalEquiv t.toAdd.val,
    (fun a z => by funext i; simp [eisensteinRationalDiagonalEquiv,
      eisensteinRationalDiagonal, mul_left_comm]),
    eisensteinRationalDiagonal_hermitian t.toAdd.val,
    eisensteinRationalDiagonal_lattice_iff t.toAdd⟩
  map_one' := by apply Subtype.ext; apply LinearEquiv.ext; exact eisensteinRationalDiagonal_zero
  map_mul' s t := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact eisensteinRationalDiagonal_add s.toAdd.val t.toAdd.val

theorem eisensteinPhaseIsometries_injective : Function.Injective eisensteinPhaseIsometries := by
  intro s t h
  change s.toAdd = t.toAdd
  apply Subtype.ext
  funext i
  apply eisensteinPhase_injective
  apply eisensteinToRational_injective
  have he := congrArg (fun f : eisensteinHermitianGroup => f.val (fun _ => 1) i) h
  change eisensteinToRational (eisensteinPhase (s.toAdd.val i)) * 1 =
    eisensteinToRational (eisensteinPhase (t.toAdd.val i)) * 1 at he
  simpa only [mul_one] using he

/-- Faithful diagonal code phases in the actual retained Co0 model. -/
def eisensteinPhasesToCo0 : Multiplicative ternaryGolay →* LeechIsometryGroup :=
  eisensteinHermitianToCo0.comp eisensteinPhaseIsometries

theorem eisensteinPhasesToCo0_injective : Function.Injective eisensteinPhasesToCo0 :=
  eisensteinHermitianToCo0_injective.comp eisensteinPhaseIsometries_injective

theorem eisensteinPhasesToCo0_mem (t : Multiplicative ternaryGolay) :
    eisensteinPhasesToCo0 t ∈ eisensteinCentralizer :=
  eisensteinHermitianToCo0_mem (eisensteinPhaseIsometries t)

/-- The actual diagonal code subgroup has order three to the sixth power. -/
theorem eisensteinPhasesToCo0_range_card : Nat.card eisensteinPhasesToCo0.range = 729 := by
  calc
    _ = Nat.card (Multiplicative ternaryGolay) :=
      (Nat.card_congr (MonoidHom.ofInjective eisensteinPhasesToCo0_injective).toEquiv).symm
    _ = 729 := ternaryGolay_card

/-- The constant codeword is exactly the distinguished scalar rho, preserving
the distinction between the full diagonal code and the scalar subgroup. -/
theorem eisensteinPhasesToCo0_oneWord :
    eisensteinPhasesToCo0 (Multiplicative.ofAdd ternaryOne) = eisensteinRho := by
  apply fullIsometryEquiv.injective
  change fullIsometryEquiv
    (eisensteinHermitianToCo0 (eisensteinPhaseIsometries (Multiplicative.ofAdd ternaryOne))) = _
  rw [eisensteinHermitianToCo0_extension, eisensteinRho_extension]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change eisensteinComparison
    (eisensteinRationalDiagonal ternaryOne.val (eisensteinComparison.symm x)) =
      eisensteinComparison (eisensteinRotation (eisensteinComparison.symm x))
  apply congrArg eisensteinComparison
  funext i
  change eisensteinToRational (eisensteinPhase 1) * (eisensteinComparison.symm x i) =
    rationalOmega * (eisensteinComparison.symm x i)
  have h : eisensteinToRational (eisensteinPhase 1) = rationalOmega := by decide +kernel
  rw [h]

end Atlas.Conway

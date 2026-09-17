import Atlas.Conway.EisensteinPhaseIsometries
import Atlas.Lattices.EisensteinMonomialOrder

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

/-- The actual coordinate permutation as a rational linear equivalence. -/
def eisensteinCoordinateEquiv (σ : Equiv.Perm (Fin 12)) :
    EisensteinRationalCoordinates ≃ₗ[ℚ] EisensteinRationalCoordinates :=
  LinearEquiv.funCongrLeft ℚ EisensteinRational σ.symm

theorem eisensteinCoordinateEquiv_embedding (σ : Equiv.Perm (Fin 12)) (z : EisensteinCoordinates) :
    eisensteinCoordinateEquiv σ (eisensteinCoordinateEmbedding z) =
      eisensteinCoordinateEmbedding (eisensteinPermutation σ z) := rfl

theorem eisensteinCoordinateEquiv_lattice (g : TernaryPureAutomorphism)
    (z : EisensteinRationalCoordinates) :
    z ∈ rationalEisensteinLattice ↔ eisensteinCoordinateEquiv g.val z ∈ rationalEisensteinLattice := by
  have hf (g : TernaryPureAutomorphism) (z : EisensteinRationalCoordinates)
      (hz : z ∈ rationalEisensteinLattice) :
      eisensteinCoordinateEquiv g.val z ∈ rationalEisensteinLattice := by
    obtain ⟨w,hw,rfl⟩ := hz
    rw [eisensteinCoordinateEquiv_embedding]
    exact ⟨_,eisensteinPermutation_mem g w hw,rfl⟩
  constructor
  · exact hf g z
  · intro hz
    have h := hf g⁻¹ _ hz
    have he : eisensteinCoordinateEquiv (g⁻¹).val (eisensteinCoordinateEquiv g.val z) = z := by
      funext i
      change z (g.val.symm (g.val i)) = z i
      rw [Equiv.symm_apply_apply]
    rw [he] at h; exact h

def eisensteinCoordinateIsometries : TernaryPureAutomorphism →* eisensteinHermitianGroup where
  toFun g := ⟨eisensteinCoordinateEquiv g.val,fun _ _ => rfl,
    eisensteinPermutation_hermitian g.val,eisensteinCoordinateEquiv_lattice g⟩
  map_one' := by apply Subtype.ext; apply LinearEquiv.ext; intro z; rfl
  map_mul' g h := by apply Subtype.ext; apply LinearEquiv.ext; intro z; rfl

/-- The global sign, kept separate from the ternary scalar subgroup. -/
def eisensteinSignIsometry : eisensteinHermitianGroup :=
  ⟨LinearEquiv.neg ℚ,fun a z => by simp,
    fun z w => by simp [eisensteinHermitian],fun z => by simp⟩

def eisensteinMonomialParameterIsometry (p : EisensteinMonomialParameters) :
    eisensteinHermitianGroup :=
  (if p.1 then eisensteinSignIsometry else 1) *
    eisensteinPhaseIsometries (Multiplicative.ofAdd p.2.1) * eisensteinCoordinateIsometries p.2.2

theorem eisensteinMonomialParameterIsometry_apply (p : EisensteinMonomialParameters)
    (z : EisensteinRationalCoordinates) (i : Fin 12) :
    (eisensteinMonomialParameterIsometry p).val z i =
      eisensteinToRational (eisensteinSignedPhase p.1 (p.2.1.val i)) * z (p.2.2.val.symm i) := by
  cases hb : p.1 <;>
    simp [eisensteinMonomialParameterIsometry,hb,eisensteinSignIsometry,
      eisensteinSignedPhase,eisensteinCoordinateIsometries,eisensteinCoordinateEquiv,
      eisensteinPhaseIsometries,eisensteinRationalDiagonalEquiv,eisensteinRationalDiagonal,
      LinearEquiv.funCongrLeft]

theorem eisensteinMonomialParameterIsometry_injective :
    Function.Injective eisensteinMonomialParameterIsometry := by
  intro p q hpq
  apply eisensteinMonomialFromParameters_injective
  apply Subtype.ext
  apply eisensteinUnitMonomial_injective
  funext z i
  apply eisensteinToRational_injective
  have h := congrArg (fun f : eisensteinHermitianGroup => f.val (eisensteinCoordinateEmbedding z) i) hpq
  simp only [eisensteinMonomialParameterIsometry_apply] at h
  change eisensteinToRational (eisensteinSignedPhase p.1 (p.2.1.val i)) *
      eisensteinToRational (z (p.2.2.val.symm i)) =
    eisensteinToRational (eisensteinSignedPhase q.1 (q.2.1.val i)) *
      eisensteinToRational (z (q.2.2.val.symm i)) at h
  simpa only [eisensteinMonomialFromParameters,eisensteinUnitMonomial,map_mul,
    eisensteinCoordinateEmbedding,eisensteinSignedPhaseUnit_val] using h

end Atlas.Conway

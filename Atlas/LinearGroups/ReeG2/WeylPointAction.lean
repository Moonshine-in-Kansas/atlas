import Atlas.LinearGroups.ReeG2.CompatiblePointSet
import Atlas.LinearGroups.ReeG2.CompatibilityReversal
import Atlas.LinearGroups.ReeG2.WeylBasePoints

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

theorem rowEquiv_upsilon (v : Vector F) :
    rowEquiv (upsilon : Ambient F) v = negativeReverse v := by
  ext i
  fin_cases i <;>
    simp [rowEquiv_apply, upsilon, upsilonMatrix, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, negativeReverse]

/-- Full Weyl preservation, obtained from the twisted exterior-square equations. -/
theorem upsilon_preserves_pointSet (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) :
    Set.MapsTo (pointRight (upsilon : Ambient F)) (pointSet m) (pointSet m) := by
  rintro p ⟨op,rfl⟩
  cases op with
  | none =>
    change pointRight upsilon infinityPoint ∈ pointSet m
    rw [pointRight_infinity_upsilon m]
    exact ⟨some (0,0,0),rfl⟩
  | some p =>
    rcases p with ⟨a,b,c⟩
    change pointRight upsilon (affinePoint m a b c) ∈ pointSet m
    unfold pointRight affinePoint
    rw [Projectivization.map_mk]
    apply compatible_mk_mem_pointSet m hcard
    change pointCompatibility m (rowEquiv upsilon (affineVector m a b c)) _
    rw [rowEquiv_upsilon]
    exact pointCompatibility_reverse m (affine_pointCompatibility m hcard a b c)

end Atlas.ReeG2

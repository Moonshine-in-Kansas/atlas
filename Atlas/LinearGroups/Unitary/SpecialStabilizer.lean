import Atlas.LinearGroups.Unitary.StandardStabilizer
import Atlas.LinearGroups.Unitary.Determinant

/-! # Actual special-unitary norm-one vector stabilizers -/
noncomputable section
namespace Atlas.Unitary
open Matrix
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

instance specialNormOneAction (hdeg : Module.finrank F K = 2) :
    MulAction (SU F K n hdeg) (NormOneVectors F K n) :=
  MulAction.compHom _ (specialInclusion hdeg)

abbrev firstSpecialStabilizer (hdeg : Module.finrank F K = 2) :=
  MulAction.stabilizer (SU F K (n + 1) hdeg)
    (coordinateUnit (F := F) (K := K) (0 : Fin (n + 1)))

theorem det_extendMatrix (A : Matrix (Fin n) (Fin n) K) :
    (extendMatrix A).det = A.det := by
  rw [Matrix.det_succ_column_zero]
  simp [extendMatrix, Fin.sum_univ_succ]
  rfl

def specialFirstInclusion (hdeg : Module.finrank F K = 2)
    (g : firstSpecialStabilizer (n := n) hdeg) : firstStabilizer (n := n) hdeg :=
  ⟨specialInclusion hdeg g.val, g.prop⟩

/-- Extend an actual special unitary matrix by the identity coordinate. -/
def extendSpecial (hdeg : Module.finrank F K = 2) (g : SU F K n hdeg) :
    firstSpecialStabilizer (n := n) hdeg :=
  ⟨⟨extendMatrix g.val, (extendUnitary hdeg (specialInclusion hdeg g)).val.prop, by
      change (extendMatrix g.val).det = 1
      rw [det_extendMatrix]
      exact g.prop.2⟩,
    (extendUnitary hdeg (specialInclusion hdeg g)).prop⟩

/-- Restrict the actual full special-unitary stabilizer to the orthogonal complement. -/
def restrictSpecial (hdeg : Module.finrank F K = 2)
    (g : firstSpecialStabilizer (n := n) hdeg) : SU F K n hdeg :=
  ⟨(restrictUnitary hdeg (specialFirstInclusion hdeg g)).val,
    (restrictUnitary hdeg (specialFirstInclusion hdeg g)).prop, by
      have he := congrArg (fun t : firstStabilizer (n := n) hdeg => t.val.val.det)
        (extend_restrict hdeg (specialFirstInclusion hdeg g))
      change (extendMatrix (restrictUnitary hdeg (specialFirstInclusion hdeg g)).val).det =
        g.val.val.det at he
      rw [det_extendMatrix] at he
      exact he.trans g.val.prop.2⟩

def firstSpecialStabilizerEquiv (hdeg : Module.finrank F K = 2) :
    firstSpecialStabilizer (n := n) hdeg ≃* SU F K n hdeg where
  toFun := restrictSpecial hdeg
  invFun := extendSpecial hdeg
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : firstStabilizer (n := n) hdeg => t.val.val)
      (extend_restrict hdeg (specialFirstInclusion hdeg g))
  right_inv g := by
    apply Subtype.ext
    exact congrArg (fun t : U F K n hdeg => t.val)
      (restrict_extend hdeg (specialInclusion hdeg g))
  map_mul' g h := by
    apply Subtype.ext
    exact congrArg (fun t : U F K n hdeg => t.val)
      ((firstStabilizerEquiv hdeg).map_mul
        (specialFirstInclusion hdeg g) (specialFirstInclusion hdeg h))

end Atlas.Unitary

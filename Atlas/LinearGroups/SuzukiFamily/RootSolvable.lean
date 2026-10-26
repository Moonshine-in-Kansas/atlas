import Atlas.LinearGroups.SuzukiFamily.GroupRelations
import Mathlib.GroupTheory.Solvable

/-! Solvability of the actual root group via its additive first coordinate. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def rootFirstHom (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    rootSubgroup m hcard →* Multiplicative F where
  toFun g := Multiplicative.ofAdd (matrix g.val 1 0)
  map_one' := by simp [Matrix.one_apply]
  map_mul' := by
    rintro ⟨g,⟨⟨a,b⟩,rfl⟩⟩ ⟨k,⟨⟨c,d⟩,rfl⟩⟩
    change Multiplicative.ofAdd (matrix (rootElement m a b * rootElement m c d) 1 0)=_
    rw [rootElement_mul m hcard]
    simp [matrix_root,u]

def rootCentralHom (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Multiplicative F →* rootSubgroup m hcard where
  toFun b := ⟨rootElement m 0 b.toAdd,⟨(0,b.toAdd),rfl⟩⟩
  map_one' := Subtype.ext (rootElement_zero m)
  map_mul' b d := by
    apply Subtype.ext
    simp [rootElement_mul m hcard]

theorem rootFirst_ker_le_central (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    (rootFirstHom m hcard).ker ≤ (rootCentralHom m hcard).range := by
  rintro ⟨g,⟨⟨a,b⟩,rfl⟩⟩ hg
  have ha : a=0 := by
    have he := congrArg Multiplicative.toAdd ((rootFirstHom m hcard).mem_ker.mp hg)
    simpa [rootFirstHom,matrix_root,u] using he
  subst a
  exact ⟨Multiplicative.ofAdd b,rfl⟩

theorem rootSubgroup_solvable (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    _root_.Group.IsSolvable (rootSubgroup m hcard) :=
  _root_.Group.isSolvable_of_ker_le_range (rootCentralHom m hcard)
    (rootFirstHom m hcard) (rootFirst_ker_le_central m hcard)
end Atlas.SuzukiFamily

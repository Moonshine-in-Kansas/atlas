import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

noncomputable section
namespace Atlas.LinearAlgebra

/-- The image of scalar multiplication by two in an arbitrary module. -/
def Doubled (M : Type*) [AddCommMonoid M] :=
  {x : M // ∃ y : M, (2 : ℕ) • y = x}

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A coordinate isomorphism identifies the doubled module coordinate by coordinate. -/
def doubledCoordinates (e : M ≃ₗ[R] (ι → R)) :
    Doubled M ≃ (ι → Doubled R) where
  toFun x i := ⟨e x.val i, by
    obtain ⟨y,hy⟩ := x.property
    exact ⟨e y i, by rw [← hy, map_nsmul]; rfl⟩⟩
  invFun x := ⟨e.symm (fun i => (x i).val), by
    choose y hy using fun i => (x i).property
    refine ⟨e.symm y, ?_⟩
    rw [← map_nsmul]
    congr 1
    funext i
    exact hy i⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv x := by
    funext i
    apply Subtype.ext
    exact congrFun (e.apply_symm_apply (fun j => (x j).val)) i

theorem doubled_zmod_four_card : Nat.card (Doubled (ZMod 4)) = 2 := by
  change Nat.card {x : ZMod 4 // ∃ y : ZMod 4, (2 : ℕ) • y = x} = 2
  rw [Nat.card_eq_fintype_card]
  decide

theorem doubled_card [Fintype ι] [Module (ZMod 4) M]
    (e : M ≃ₗ[ZMod 4] (ι → ZMod 4)) : Nat.card (Doubled M) = 2 ^ Fintype.card ι := by
  rw [Nat.card_congr (doubledCoordinates e)]
  simp [Nat.card_fun, doubled_zmod_four_card]

end Atlas.LinearAlgebra

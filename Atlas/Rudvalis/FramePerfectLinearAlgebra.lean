import Atlas.Rudvalis.CodeRowExact
import Mathlib.GroupTheory.IsPerfect

namespace Atlas.Rudvalis
open scoped BigOperators

/-- Reuse elementary generation and commutators of the already verified special linear family. -/
theorem binaryLinearGroup_perfect : Group.IsPerfect (E ≃ₗ[Bit] E) := by
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) Bit) := Atlas.sl_perfect 3 (by decide)
  exact Group.IsPerfect.ofSurjective binarySLToLinear_surjective

def affineRowSign (a : Bit) (v : E) : Point→Bit := fun p=>a+dot v p.val

theorem affineRowSign_mem (a : Bit) (v : E) : affineRowSign a v∈hammingSignCode := by
  change rowMoment (affineRowSign a v)=0
  decide +kernel +revert

def affineRowSignLinear : (Bit×E) →ₗ[Bit] hammingSignCode where
  toFun z := ⟨affineRowSign z.1 z.2,affineRowSign_mem z.1 z.2⟩
  map_add' z w := by
    apply Subtype.ext
    funext p
    change (z.1+w.1)+dot (z.2+w.2) p.val=(z.1+dot z.2 p.val)+(w.1+dot w.2 p.val)
    rw [dot_add_left]
    abel
  map_smul' a z := by
    apply Subtype.ext
    funext p
    change a*z.1+dot (a • z.2) p.val=a*(z.1+dot z.2 p.val)
    simp [dot,Finset.mul_sum,mul_add,mul_assoc]

theorem affineRowSign_injective : Function.Injective affineRowSignLinear := by
  intro z w h
  have hh : affineRowSign z.1 z.2=affineRowSign w.1 w.2 := congrArg Subtype.val h
  have cert : ∀a b : Bit,∀v w : E,affineRowSign a v=affineRowSign b w → a=b ∧ v=w := by
    decide +kernel
  exact Prod.ext (cert _ _ _ _ hh).1 (cert _ _ _ _ hh).2

theorem affineRowSign_surjective : Function.Surjective affineRowSignLinear := by
  apply (Nat.bijective_iff_injective_and_card _).mpr ⟨affineRowSign_injective,?_⟩ |>.2
  rw [hammingSignCode_card,Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card,Bit,ZMod.card,card_E]

end Atlas.Rudvalis

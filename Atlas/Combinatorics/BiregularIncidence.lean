import Mathlib.Data.Fintype.Sigma
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Module.NatInt

namespace Atlas.Combinatorics
open scoped BigOperators

/-- Double-count a finite relation whose two families of fibres have constant sizes. -/
theorem uniform_incidence_card {A B : Type*} [Finite A] [Finite B]
    (r : A→B→Prop) (a b : ℕ)
    (ha : ∀x : A,Nat.card {y : B // r x y}=a)
    (hb : ∀y : B,Nat.card {x : A // r x y}=b) :
    Nat.card A*a=Nat.card B*b := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  let e : (Σx : A,{y : B // r x y}) ≃ Σy : B,{x : A // r x y} :=
    {toFun := fun z=>⟨z.2.val,z.1,z.2.prop⟩
     invFun := fun z=>⟨z.2.val,z.1,z.2.prop⟩
     left_inv := fun _=>rfl
     right_inv := fun _=>rfl}
  have h := Nat.card_congr e
  rw [Nat.card_sigma,Nat.card_sigma] at h
  simp_rw [ha,hb] at h
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card] using h

end Atlas.Combinatorics

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! finite sign-parity arithmetic for D half-spin labels.
This file counts actual sign patterns, not desired groups or assumed orbits. -/
namespace Atlas.Chevalley.Integral.Minuscule.DParity
open Classical
noncomputable section

def sign (b : Bool) : ℤ := if b then 1 else -1

@[simp] theorem sign_sq (b : Bool) : sign b * sign b = 1 := by cases b <;> decide

def product {r : ℕ} (σ : Fin r → Bool) : ℤ := ∏ k, sign (σ k)

theorem product_cases {r : ℕ} (σ : Fin r → Bool) : product σ=1 ∨ product σ= -1 := by
  have h : ∀ s : Finset (Fin r), (∏ k ∈ s, sign (σ k))=1 ∨ (∏ k ∈ s, sign (σ k))= -1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      rcases ih with h | h <;> rw [h] <;> cases σ i <;> norm_num [sign]
  exact h Finset.univ

theorem product_sq {r : ℕ} (σ : Fin r → Bool) : product σ * product σ = 1 := by
  rcases product_cases σ with h | h <;> rw [h] <;> norm_num

/-- A parity label specifies its sign product, +1 or -1. -/
abbrev Fiber (r : ℕ) (ε : Bool) := {σ : Fin r → Bool // product σ=sign ε}

/-- Fill the first sign uniquely to achieve the prescribed product. -/
def complete (r : ℕ) (ε : Bool) (τ : Fin r → Bool) : Fin (r+1) → Bool :=
  Fin.cons (decide (sign ε * product τ = 1)) τ

theorem complete_head (r : ℕ) (ε : Bool) (τ : Fin r → Bool) :
    sign (complete r ε τ 0) = sign ε * product τ := by
  rcases product_cases τ with h | h <;> cases ε <;> simp [complete, sign, h]

theorem product_complete (r : ℕ) (ε : Bool) (τ : Fin r → Bool) :
    product (complete r ε τ) = sign ε := by
  rw [product, Fin.prod_univ_succ]
  change sign (complete r ε τ 0) * product τ = sign ε
  rw [complete_head, mul_assoc, product_sq, mul_one]

/-- Exactly one free bit is removed by prescribing the parity. -/
def fiberEquiv (r : ℕ) (ε : Bool) : (Fin r → Bool) ≃ Fiber (r+1) ε where
  toFun τ := ⟨complete r ε τ, product_complete r ε τ⟩
  invFun σ := fun k => σ.val k.succ
  left_inv τ := rfl
  right_inv σ := by
    apply Subtype.ext
    funext k
    refine Fin.cases ?_ (fun j => rfl) k
    have hp := σ.property
    rw [product, Fin.prod_univ_succ] at hp
    have ht := product_sq (fun k : Fin r => σ.val k.succ)
    have he : sign (σ.val 0) = sign ε * product (fun k : Fin r => σ.val k.succ) := by
      change sign (σ.val 0) * product (fun k : Fin r => σ.val k.succ) = sign ε at hp
      calc
        sign (σ.val 0) = sign (σ.val 0) *
            (product (fun k : Fin r => σ.val k.succ) * product (fun k : Fin r => σ.val k.succ)) := by
          rw [ht, mul_one]
        _ = (sign (σ.val 0) * product (fun k : Fin r => σ.val k.succ)) *
            product (fun k : Fin r => σ.val k.succ) := (mul_assoc _ _ _).symm
        _ = sign ε * product (fun k : Fin r => σ.val k.succ) :=
          congrArg (· * product (fun k : Fin r => σ.val k.succ)) hp
    change decide (sign ε * product (fun k : Fin r => σ.val k.succ)=1) = σ.val 0
    rw [← he]
    cases σ.val 0 <;> simp [sign]

theorem fiber_card (r : ℕ) (ε : Bool) : Nat.card (Fiber (r+1) ε)=2^r := by
  rw [← Nat.card_congr (fiberEquiv r ε)]
  simp

end
end Atlas.Chevalley.Integral.Minuscule.DParity

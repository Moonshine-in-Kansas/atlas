import Atlas.LinearGroups.Chevalley.Integral.MinusculeDParity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Logic.Relation

/-! signed-pair moves preserving the actual D parity fibres. -/
namespace Atlas.Chevalley.Integral.Minuscule.DParity
open Classical
noncomputable section

def flip {r : ℕ} (σ : Fin r → Bool) (i : Fin r) : Fin r → Bool :=
  Function.update σ i (!(σ i))

def pairFlip {r : ℕ} (σ : Fin r → Bool) (i j : Fin r) : Fin r → Bool := flip (flip σ i) j

theorem product_flip {r : ℕ} (σ : Fin r → Bool) (i : Fin r) : product (flip σ i) = -product σ := by
  have he : (fun k => sign (flip σ i k)) = Function.update (fun k => sign (σ k)) i (-sign (σ i)) := by
    funext k
    by_cases hk : k=i
    · subst k; cases h : σ i <;> simp [flip, sign, h]
    · simp [flip, hk]
  have h₀ := Finset.prod_update_of_mem (s := Finset.univ) (Finset.mem_univ i)
    (fun k => sign (σ k)) (sign (σ i))
  simp only [Function.update_eq_self] at h₀
  rw [product, he, Finset.prod_update_of_mem (Finset.mem_univ i), neg_mul, ← h₀]
  rfl

theorem product_pairFlip {r : ℕ} (σ : Fin r → Bool) (i j : Fin r) :
    product (pairFlip σ i j) = product σ := by
  simp [pairFlip, product_flip]

def swap {r : ℕ} (σ : Fin r → Bool) (i j : Fin r) : Fin r → Bool :=
  fun k => σ (Equiv.swap i j k)

theorem product_swap {r : ℕ} (σ : Fin r → Bool) (i j : Fin r) :
    product (swap σ i j) = product σ :=
  Equiv.prod_comp (Equiv.swap i j) (fun k => sign (σ k))

/-- For equal root signs negate the exchanged pair; for opposite signs just exchange. -/
def signedSwap {r : ℕ} (σ : Fin r → Bool) (i j : Fin r) (negate : Bool) : Fin r → Bool :=
  if negate then pairFlip (swap σ i j) i j else swap σ i j

theorem product_signedSwap {r : ℕ} (σ : Fin r → Bool) (i j : Fin r) (negate : Bool) :
    product (signedSwap σ i j negate) = product σ := by
  cases negate <;> simp [signedSwap, product_pairFlip, product_swap]

/-- Equality off one coordinate and equal product force equality at that coordinate too. -/
theorem eq_of_product_and_off {r : ℕ} (p : Fin r) (σ τ : Fin r → Bool)
    (hp : product σ=product τ) (hoff : ∀ i, i≠p → σ i=τ i) : σ=τ := by
  have hσ := Finset.mul_prod_erase Finset.univ (fun k => sign (σ k)) (Finset.mem_univ p)
  have hτ := Finset.mul_prod_erase Finset.univ (fun k => sign (τ k)) (Finset.mem_univ p)
  have ht : (∏ k ∈ Finset.univ.erase p, sign (σ k)) =
      ∏ k ∈ Finset.univ.erase p, sign (τ k) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [hoff k (Finset.mem_erase.mp hk).1]
  have hn : (∏ k ∈ Finset.univ.erase p, sign (τ k)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    cases τ k <;> norm_num [sign]
  have he : sign (σ p)=sign (τ p) := by
    apply mul_right_cancel₀ hn
    calc
      sign (σ p) * (∏ k ∈ Finset.univ.erase p, sign (τ k)) =
          sign (σ p) * (∏ k ∈ Finset.univ.erase p, sign (σ k)) := congrArg (sign (σ p) * ·) ht.symm
      _ = sign (τ p) * (∏ k ∈ Finset.univ.erase p, sign (τ k)) := hσ.trans (hp.trans hτ.symm)
  funext k
  by_cases hk : k=p
  · subst k
    cases hs : σ p <;> cases ht : τ p <;> first | rfl | (norm_num [sign, hs, ht] at he)
  · exact hoff k hk

def PairStep {r : ℕ} (σ τ : Fin r → Bool) : Prop :=
  ∃ i j : Fin r, i≠j ∧ τ=pairFlip σ i j

/-- Fix each non-pivot coordinate by a pair flip; parity then fixes the pivot. -/
theorem pair_reachable {r : ℕ} (p : Fin r) (σ τ : Fin r → Bool) (hp : product σ=product τ) :
    Relation.ReflTransGen PairStep σ τ := by
  have aux : ∀ s : Finset (Fin r), p∉s → ∀ σ τ : Fin r → Bool,
      product σ=product τ → (∀ i, i∉s → i≠p → σ i=τ i) →
      Relation.ReflTransGen PairStep σ τ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ σ τ hp h
      have he := eq_of_product_and_off p σ τ hp (fun i hi => h i (by simp) hi)
      rw [he]
    | @insert i s hi ih =>
      intro hps σ τ hp h
      have hip : i≠p := by intro he; subst i; simp at hps
      have hps' : p∉s := by
        intro hp
        exact hps (Finset.mem_insert_of_mem hp)
      by_cases he : σ i=τ i
      · apply ih hps' σ τ hp
        intro k hk hkp
        by_cases hki : k=i
        · subst k; exact he
        · exact h k (by simp [hk,hki]) hkp
      · let σ' := pairFlip σ i p
        have hprod : product σ'=product τ := (product_pairFlip σ i p).trans hp
        have hrest : ∀ k, k∉s → k≠p → σ' k=τ k := by
          intro k hk hkp
          by_cases hki : k=i
          · subst k
            have ht : τ i= !(σ i) := by cases hs : σ i <;> cases ht : τ i <;> simp_all
            simp [σ',pairFlip,flip,hip,ht]
          · simpa [σ',pairFlip,flip,hki,hkp] using h k (by simp [hk,hki]) hkp
        exact (Relation.ReflTransGen.single ⟨i,p,hip,rfl⟩).trans (ih hps' σ' τ hprod hrest)
  apply aux (Finset.univ.erase p) (by simp) σ τ hp
  intro i hi hip
  exact False.elim (hi (by simp [hip]))

end
end Atlas.Chevalley.Integral.Minuscule.DParity

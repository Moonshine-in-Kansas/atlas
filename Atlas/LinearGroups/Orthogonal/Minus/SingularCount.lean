import Atlas.LinearGroups.Orthogonal.Minus.Basic
import Atlas.LinearAlgebra.DotProductFiber
import Atlas.LinearAlgebra.QuadraticZeroCount

/-! Singular vectors in the nonsplit norm-plane form, counted without group orders. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Atlas.Orthogonal.Minus
open Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {k : ℕ}

abbrev Remaining (x : Fin k → F) :=
  {p : (Fin k → F) × K // Atlas.DotProduct.functional x p.1 + norm F K p.2 = 0}

def remainingZeroEquiv (hdeg : Module.finrank F K = 2) :
    Remaining (K := K) (0 : Fin k → F) ≃ (Fin k → F) where
  toFun p := p.val.1
  invFun y := ⟨(y,0),by simp⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hz : norm F K p.val.2 = 0 := by simpa using p.prop
      exact ((norm_zero_iff hdeg _).mp hz).symm
  right_inv _ := rfl

def remainingEquiv (x : Fin k → F) : Remaining (K := K) x ≃
    Σ z : K, {y : Fin k → F // Atlas.DotProduct.functional x y = -norm F K z} where
  toFun p := ⟨p.val.2,⟨p.val.1,eq_neg_of_add_eq_zero_left p.prop⟩⟩
  invFun p := ⟨(p.2.val,p.1),by rw [p.2.prop]; ring⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_remaining (hdeg : Module.finrank F K = 2) (x : Fin k → F) :
    Nat.card (Remaining (K := K) x) =
      if x = 0 then Nat.card F ^ k else Nat.card F ^ (k+1) := by
  classical
  letI := Fintype.ofFinite K
  by_cases hx : x = 0
  · subst x
    simp only [ite_true]
    rw [Nat.card_congr (remainingZeroEquiv hdeg), Nat.card_fun, Nat.card_fin]
  · rw [if_neg hx, Nat.card_congr (remainingEquiv (K := K) x), Nat.card_sigma]
    simp_rw [Atlas.DotProduct.card_fiber x hx]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, Nat.cast_id]
    rw [card_extension hdeg, ← pow_add]
    congr 1
    have hk : 0 < k := by
      by_contra h
      have : k = 0 := by omega
      subst k
      exact hx (Subsingleton.elim _ _)
    omega

def singularFiberEquiv (hdeg : Module.finrank F K = 2) :
    {v : Vector k F K // form hdeg k v = 0} ≃ Σ x : Fin k → F, Remaining (K := K) x where
  toFun v := ⟨fun i => v.val.1 (.inl i),⟨(fun i => v.val.1 (.inr i),v.val.2),by
    simpa only [Atlas.DotProduct.functional_apply, form_apply, formD_apply] using v.prop⟩⟩
  invFun p := ⟨(Sum.elim p.1 p.2.val.1,p.2.val.2),by
    simpa only [form_apply,formD_apply,Sum.elim_inl,Sum.elim_inr,
      Atlas.DotProduct.functional_apply] using p.2.prop⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · funext i; cases i <;> rfl
    · rfl
  right_inv _ := rfl

theorem card_singular (hdeg : Module.finrank F K = 2) (k : ℕ) :
    Nat.card {v : Vector k F K // form hdeg k v = 0} =
      Nat.card F ^ k + (Nat.card F ^ k - 1) * Nat.card F ^ (k+1) := by
  classical
  letI := Fintype.ofFinite F
  rw [Nat.card_congr (singularFiberEquiv hdeg), Nat.card_sigma]
  simp_rw [card_remaining hdeg]
  rw [Finset.sum_ite]
  have hz : (Finset.univ.filter fun x : Fin k → F => x = 0) = {0} := by ext x; simp
  simp [hz,Finset.filter_ne',Nat.card_eq_fintype_card]

abbrev NonzeroSingular (hdeg : Module.finrank F K = 2) (k : ℕ) :=
  {v : {x : Vector k F K // form hdeg k x = 0} // v.val ≠ 0}

theorem card_nonzero_singular (hdeg : Module.finrank F K = 2) (k : ℕ) :
    Nat.card (NonzeroSingular hdeg k) = (Nat.card F ^ (k+1)+1) * (Nat.card F ^ k-1) := by
  rw [Atlas.Quadratic.card_nonzero_singular, card_singular, add_mul, one_mul]
  have h : 1 ≤ Nat.card F ^ k := one_le_pow₀ (by have := Finite.one_lt_card (α := F); omega)
  rw [mul_comm (Nat.card F ^ (k+1))]
  omega
end Atlas.Orthogonal.Minus

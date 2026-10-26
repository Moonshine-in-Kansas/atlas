import Atlas.LinearGroups.Unitary.Hermitian
import Mathlib.Algebra.CharP.Two

/-! Scalar identities for a genuine quadratic extension of the binary field. -/
noncomputable section
namespace Atlas.Unitary
open Atlas.FiniteQuadratic
open scoped Classical
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem binary_pow_four (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2)
    (x : K) : x ^ 4 = x := by
  have hc : Nat.card K = 4 := by rw [card_extension hdeg, hq]; decide
  letI := Fintype.ofFinite K
  simpa only [← Nat.card_eq_fintype_card, hc] using FiniteField.pow_card x

theorem binary_nonzero_cube (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2)
    (x : K) (hx : x ≠ 0) : x ^ 3 = 1 := by
  apply mul_right_cancel₀ hx
  calc
    x ^ 3 * x = x ^ 4 := by ring
    _ = x := binary_pow_four hdeg hq x
    _ = 1 * x := (one_mul x).symm

theorem binary_nonzero_norm (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2)
    (x : K) (hx : x ≠ 0) : x * conjugation F K x = 1 := by
  rw [conjugation_apply, hq]
  calc
    x * x ^ 2 = x ^ 3 := by ring
    _ = 1 := binary_nonzero_cube hdeg hq x hx

theorem binary_norm_entry (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2)
    (x : K) : x * conjugation F K x = if x = 0 then 0 else 1 := by
  classical
  split_ifs with hx
  · simp [hx]
  · exact binary_nonzero_norm hdeg hq x hx

theorem binary_hermitian_support_sum (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) {n : ℕ} (v : Fin n → K) :
    hermitian F K v v = ∑ i, if v i = 0 then 0 else 1 := by
  classical
  exact Finset.sum_congr rfl (fun i _ => binary_norm_entry hdeg hq (v i))

theorem binary_charP (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2) :
    CharP K 2 := by
  letI := Fintype.ofFinite K
  apply ringChar.of_eq
  apply FiniteField.even_card_iff_char_two.mpr
  have hc : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, card_extension hdeg, hq]
    decide
  rw [hc]

theorem exists_binary_primitive (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) : ∃ c : K, c ^ 2 + c + 1 = 0 := by
  classical
  letI := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, card_extension hdeg, hq]
    decide
  have hex : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
    by_contra h
    push_neg at h
    have hs : Finset.univ ⊆ ({0,1} : Finset K) := by
      intro x _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr (h x hx)
    have he := Finset.card_le_card hs
    simpa [hcard] using he
  obtain ⟨c,hc0,hc1⟩ := hex
  refine ⟨c, ?_⟩
  have hprod : (c-1)*(c^2+c+1)=0 := by
    calc
      (c-1)*(c^2+c+1) = c^3-1 := by ring
      _ = 0 := by rw [binary_nonzero_cube hdeg hq c hc0, sub_self]
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hc1)

end Atlas.Unitary

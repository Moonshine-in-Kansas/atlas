import Atlas.Conway.MinimalOddOrbit
import Atlas.Lattices.LeechShortShellCounts

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem odd_base_no_constant_orthogonal_minimum (a : Omega) (x : IntegerCoordinates)
    (b : ℤ) (hb : ∀ i, i ≠ a → x i = b)
    (ho : integerDot (oddProfileBase {a} ∅) x = 0)
    (hn : integerDot x x = 32) : False := by
  have hcard : (Finset.univ.erase a).card = 23 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    decide
  have hs : (∑ i ∈ Finset.univ.erase a, x i) = 23*b := by
    rw [Finset.sum_congr rfl (fun i hi => hb i (Finset.mem_erase.mp hi).1)]
    simp [hcard]
  have hdot : integerDot (oddProfileBase {a} ∅) x = -3*x a + 23*b := by
    unfold integerDot
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
    have hr : (∑ i ∈ Finset.univ.erase a, oddProfileBase {a} ∅ i * x i) = 23*b := by
      rw [← hs]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := (Finset.mem_erase.mp hi).1
      simp [oddProfileBase,hi']
    rw [hr]
    simp [oddProfileBase]
  have hbound : x a * x a ≤ 32 := by
    rw [← hn]
    exact Finset.single_le_sum (fun i _ => mul_self_nonneg (x i)) (Finset.mem_univ a)
  have hxa : -5 ≤ x a ∧ x a ≤ 5 := by constructor <;> nlinarith
  have he : 3*x a = 23*b := by rw [hdot] at ho; omega
  have hb0 : b = 0 := by omega
  have ha0 : x a = 0 := by omega
  have hx0 : x = 0 := by
    funext i
    by_cases hi : i = a
    · simpa [hi] using ha0
    · simpa [hb0] using hb i hi
  simp [hx0,integerDot] at hn

end Atlas.Conway

import Atlas.Lattices.EisensteinClassBounds
import Atlas.Combinatorics.FiniteImageCapacity

noncomputable section
namespace Atlas.Lattices
open Atlas.Combinatorics
attribute [local instance] Classical.propDecidable

instance eisensteinShell_fintype (r : ℤ) : Fintype (EisensteinShell r) := by
  letI : Fintype (LeechShell r) := Fintype.ofFinite _
  exact Fintype.ofEquiv (LeechShell r) (eisensteinShellEquiv r).symm

instance eisensteinClasses_fintype : Fintype EisensteinClasses := by
  letI : Finite EisensteinClasses := Nat.finite_of_card_ne_zero (by rw [eisensteinClasses_card]; decide)
  exact Fintype.ofFinite _

def eisensteinShellClasses (r : ℤ) : Finset EisensteinClasses :=
  Finset.univ.image (fun x : EisensteinShell r => eisensteinClass x.val)

theorem eisensteinShellClasses_capacity (r : ℤ) (n : ℕ)
    (hb : ∀ c, Nat.card (EisensteinClassFiber r c) ≤ n) :
    Nat.card (EisensteinShell r) ≤ n*(eisensteinShellClasses r).card :=
  card_le_capacity_mul_image (fun x : EisensteinShell r => eisensteinClass x.val) n hb

theorem eisensteinShellClasses_zero_not_mem (r : ℤ) (hr : 0<r ∧ r<12) :
    0 ∉ eisensteinShellClasses r := by
  intro h
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h
  apply eisenstein_short_class_ne_zero x.val ?_ ?_ hx
  · rw [x.property]; exact_mod_cast hr.1
  · rw [x.property]; exact_mod_cast hr.2

theorem eisensteinShellClasses_disjoint :
    Disjoint (eisensteinShellClasses 4) (eisensteinShellClasses 6) := by
  apply Finset.disjoint_left.mpr
  intro c hc hd
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hc
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hd
  exact eisenstein_four_six_differentClass x.val y.val x.property y.property (hx.trans hy.symm)

def eisensteinShortClasses : Finset EisensteinClasses :=
  {0} ∪ (eisensteinShellClasses 4 ∪ eisensteinShellClasses 6)

theorem eisensteinShortClasses_card : eisensteinShortClasses.card =
    1+(eisensteinShellClasses 4).card+(eisensteinShellClasses 6).card := by
  have h0 : Disjoint ({0} : Finset EisensteinClasses)
      (eisensteinShellClasses 4 ∪ eisensteinShellClasses 6) := by
    apply Finset.disjoint_singleton_left.mpr
    simp only [Finset.mem_union, not_or]
    exact ⟨eisensteinShellClasses_zero_not_mem 4 (by decide),
      eisensteinShellClasses_zero_not_mem 6 (by decide)⟩
  rw [eisensteinShortClasses, Finset.card_union_of_disjoint h0,
    Finset.card_union_of_disjoint eisensteinShellClasses_disjoint, Finset.card_singleton]
  omega

/-- Saturation of the independently counted quotient forces both class counts. -/
theorem eisensteinShellClasses_counts :
    (eisensteinShellClasses 4).card = 65520 ∧ (eisensteinShellClasses 6).card = 465920 := by
  have h4 := eisensteinShellClasses_capacity 4 3 eisenstein_four_class_card_le
  have h6 := eisensteinShellClasses_capacity 6 36 eisenstein_six_class_card_le
  rw [eisensteinShell_four_card] at h4
  rw [eisensteinShell_six_card] at h6
  have ht := Finset.card_le_univ eisensteinShortClasses
  rw [eisensteinShortClasses_card, ← Nat.card_eq_fintype_card, eisensteinClasses_card] at ht
  omega

theorem eisensteinShortClasses_eq_univ : eisensteinShortClasses = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [eisensteinShortClasses_card, eisensteinShellClasses_counts.1,
    eisensteinShellClasses_counts.2, ← Nat.card_eq_fintype_card, eisensteinClasses_card]

/-- Every occupied norm-six class reaches the 36-vector geometric capacity. -/
theorem eisenstein_six_class_card (c : EisensteinClasses)
    (hc : c ∈ eisensteinShellClasses 6) : Nat.card (EisensteinClassFiber 6 c) = 36 := by
  apply fiber_eq_capacity_of_saturation
    (fun x : EisensteinShell 6 => eisensteinClass x.val) 36 eisenstein_six_class_card_le ?_ c hc
  change Nat.card (EisensteinShell 6) = 36*(eisensteinShellClasses 6).card
  rw [eisensteinShell_six_card, eisensteinShellClasses_counts.2]

end Atlas.Lattices

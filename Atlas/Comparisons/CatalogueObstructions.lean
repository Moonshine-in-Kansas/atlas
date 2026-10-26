import Atlas.Comparisons.CatalogueNormalization
import Atlas.Comparisons.Classical.OrthogonalInvolutions
import Atlas.Comparisons.Exceptional.Order20160Nonisomorphism

noncomputable section
namespace Atlas.Comparisons.Catalogue
open Atlas.OrderArithmetic

private theorem linear_fiber (x : Entry) (d q : ℕ) (h : label x = .linear d q) :
    ∃ F : FiniteField, Nat.card F.carrier = q ∧
      Nonempty (Model x ≃* Matrix.ProjectiveSpecialLinearGroup (Fin d) F.carrier) := by
  cases x with
  | linear F n hx =>
    have hh : n = d ∧ Nat.card F.carrier = q := by simpa only [label, RawEntry.linear.injEq] using h
    rcases hh with ⟨rfl, hq⟩
    exact ⟨F, hq, ⟨MulEquiv.refl _⟩⟩
  | _ => simp [label] at h

private theorem alternating_fiber (x : Entry) (n : ℕ) (h : label x = .alternating n) :
    Nonempty (Model x ≃* alternatingGroup (Fin n)) := by
  cases x with
  | alternating m hm =>
    have hh : m = n := by simpa only [label, RawEntry.alternating.injEq] using h
    subst m
    exact ⟨MulEquiv.refl _⟩
  | _ => simp [label] at h

private theorem B_fiber (x : Entry) (r q : ℕ) (h : label x = .B r q) :
    ∃ F : FiniteField, Nat.card F.carrier = q ∧
      Nonempty (Model x ≃* Atlas.Orthogonal.B r F.carrier) := by
  cases x with
  | B F n hx =>
    have hh : n = r ∧ Nat.card F.carrier = q := by simpa only [label, RawEntry.B.injEq] using h
    rcases hh with ⟨rfl, hq⟩
    exact ⟨F, hq, ⟨MulEquiv.refl _⟩⟩
  | _ => simp [label] at h

private theorem C_fiber (x : Entry) (r q : ℕ) (h : label x = .C r q) :
    ∃ F : FiniteField, Nat.card F.carrier = q ∧
      Nonempty (Model x ≃* Atlas.Symplectic.PSp r F.carrier) := by
  cases x with
  | C F n hx =>
    have hh : n = r ∧ Nat.card F.carrier = q := by simpa only [label, RawEntry.C.injEq] using h
    rcases hh with ⟨rfl, hq⟩
    exact ⟨F, hq, ⟨MulEquiv.refl _⟩⟩
  | _ => simp [label] at h

private theorem odd_field_two_ne_zero (F : FiniteField) (h : Odd (Nat.card F.carrier)) :
    (2 : F.carrier) ≠ 0 := by
  intro h2
  letI : Fintype F.carrier := Fintype.ofFinite _
  letI : CharP F.carrier 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have he := FiniteField.even_card_of_char_two (F := F.carrier) (ringChar.eq _ 2)
  have ho := Nat.odd_iff.mp h
  rw [Nat.card_eq_fintype_card] at ho
  omega

/-- The two arithmetic equal-order exceptions are actual non-isomorphisms.
This uses the established Sylow-center and involution-class obstructions. -/
theorem exceptional_not_isomorphic (x y : Entry)
    (h : OrderArithmetic.Exceptional (label x) (label y)) :
    ¬ Nonempty (Model x ≃* Model y) := by
  have hA (u v : Entry) (hu : label u = .alternating 8) (hv : label v = .linear 3 4) :
      ¬ Nonempty (Model u ≃* Model v) := by
    obtain ⟨eu⟩ := alternating_fiber u 8 hu
    obtain ⟨F, hF, ⟨ev⟩⟩ := linear_fiber v 3 4 hv
    rintro ⟨e⟩
    exact Exceptional.alt8_not_equiv_psl3Card4 hF ⟨eu.symm.trans (e.trans ev)⟩
  have hBC (u v : Entry) (r q : ℕ) (hr : 3 ≤ r) (hq : Odd q)
      (hu : label u = .B r q) (hv : label v = .C r q) :
      ¬ Nonempty (Model u ≃* Model v) := by
    obtain ⟨F, hF, ⟨eu⟩⟩ := B_fiber u r q hu
    obtain ⟨K, hK, ⟨ev⟩⟩ := C_fiber v r q hv
    let ef := SameFieldSize.fieldEquiv (hK.trans hF.symm)
    let ec := Atlas.Symplectic.fieldEquivPSp (n := r) ef
    have h2 := odd_field_two_ne_zero F (by simpa only [hF] using hq)
    rintro ⟨e⟩
    exact Classical.oddB_not_equiv_C r hr h2 ⟨eu.symm.trans (e.trans (ev.trans ec))⟩
  rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩ | ⟨r, q, hr, hq, ho, hbc⟩
  · exact hA x y hx hy
  · rintro ⟨e⟩; exact hA y x hy hx ⟨e.symm⟩
  · rcases hbc with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · exact hBC x y r q hr ho hx hy
    · rintro ⟨e⟩; exact hBC y x r q hr ho hy hx ⟨e.symm⟩

end Atlas.Comparisons.Catalogue

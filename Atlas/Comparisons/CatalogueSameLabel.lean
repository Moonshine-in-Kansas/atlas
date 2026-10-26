import Atlas.Comparisons.CatalogueModels
import Atlas.Comparisons.SameFieldSize

/-! Equality of catalogue labels is realized by actual coordinate transport. -/
noncomputable section
namespace Atlas.Comparisons.Catalogue
open Atlas.OrderArithmetic

private theorem fixed_label_injective : Function.Injective Fixed.label := by
  intro x y h
  cases x <;> cases y <;> simp_all [Fixed.label]

/-- No finite-field representation or extension presentation affects the group. -/
theorem same_label_equiv (x y : Entry) (h : label x = label y) :
    Nonempty (Model x ≃* Model y) := by
  cases x <;> cases y <;>
    simp only [label, RawEntry.cyclic.injEq, RawEntry.alternating.injEq,
      RawEntry.linear.injEq, RawEntry.unitary.injEq, RawEntry.B.injEq,
      RawEntry.C.injEq, RawEntry.Dplus.injEq, RawEntry.Dminus.injEq,
      RawEntry.G2.injEq, RawEntry.F4.injEq, RawEntry.trialityD4.injEq,
      RawEntry.suzuki.injEq, RawEntry.smallRee.injEq, RawEntry.fixed.injEq,
      reduceCtorEq] at h
  · subst_vars
    exact ⟨MulEquiv.refl _⟩
  · subst_vars
    exact ⟨MulEquiv.refl _⟩
  · rename_i F d hd E e he
    rcases h with ⟨rfl, hc⟩
    exact ⟨Atlas.fieldEquivPSL d (SameFieldSize.fieldEquiv hc)⟩
  · rename_i F d hd E e he
    rcases h with ⟨rfl, hc⟩
    exact ⟨Atlas.Unitary.projectiveUnitaryEquivOfBaseCardEq F.finrank E.finrank hc d⟩
  · rename_i F d hd E e he
    rcases h with ⟨rfl, hc⟩
    exact ⟨Atlas.Orthogonal.B_fieldEquiv d (SameFieldSize.fieldEquiv hc)⟩
  · rename_i F d hd E e he
    rcases h with ⟨rfl, hc⟩
    exact ⟨Atlas.Symplectic.fieldEquivPSp (n := d) (SameFieldSize.fieldEquiv hc)⟩
  · rename_i F d hd E e he
    rcases h with ⟨rfl, hc⟩
    exact ⟨Atlas.Orthogonal.DPlus_fieldEquiv d (SameFieldSize.fieldEquiv hc)⟩
  · rename_i F d hd E e he
    rcases h with ⟨rfl, hc⟩
    exact ⟨SameFieldSize.minusEquiv F.finrank E.finrank hc d⟩
  · exact ⟨Atlas.G2.fieldEquiv (SameFieldSize.fieldEquiv h)⟩
  · exact ⟨Atlas.F4.fieldTransport (SameFieldSize.fieldEquiv h)⟩
  · rename_i F hf E he
    exact ⟨SameFieldSize.trialityEquiv F.finrank E.finrank h⟩
  · rename_i F m hm hF E n hn hE
    have hp : 2 * m + 1 = 2 * n + 1 :=
      Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) (hF.symm.trans (h.trans hE))
    have hmn : m = n := by omega
    subst n
    exact ⟨Atlas.SuzukiFamily.fieldEquiv (SameFieldSize.fieldEquiv h) m⟩
  · rename_i F m hm hF E n hn hE
    have hp : 2 * m + 1 = 2 * n + 1 :=
      Nat.pow_right_injective (by decide : 2 ≤ (3 : ℕ)) (hF.symm.trans (h.trans hE))
    have hmn : m = n := by omega
    subst n
    exact ⟨Atlas.ReeG2.fieldEquiv (SameFieldSize.fieldEquiv h) m⟩
  · have he := fixed_label_injective h
    subst_vars
    exact ⟨MulEquiv.refl _⟩

end Atlas.Comparisons.Catalogue

import Atlas.Conway.GolayOctadExteriorRestriction
import Atlas.Fischer.SignedOctads
import Atlas.Fischer.Cocode

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Conway Atlas.Lattices
open scoped BigOperators

/-- The actual Golay words vanishing on the marked octad. -/
def octadShortenedCode (O : Octad) : Submodule Bit golay :=
  (golayRestriction O.val).ker

@[simp] theorem mem_octadShortenedCode (O : Octad) (c : golay) :
    c ∈ octadShortenedCode O ↔ ∀ i ∈ O.val, c.val i = 0 := by
  change golayRestriction O.val c = 0 ↔ _
  constructor
  · intro h i hi
    exact congrFun h ⟨i,hi⟩
  · intro h
    funext i
    exact h i.val i.prop

/-- The retained complement word, not a new binary code. -/
def octadComplementWord (O : Octad) : golay := golayOne + octadWord O

theorem octadWord_apply (O : Octad) (i : Omega) :
    (octadWord O).val i = if i ∈ O.val then 1 else 0 := by
  classical
  have h : (octadWord O).val i ≠ 0 ↔ i ∈ O.val := by
    rw [← octadWord_support O]
    simp [support]
  by_cases hi : i ∈ O.val
  · simp only [hi, if_true]
    have hb : ∀ b : Bit, b ≠ 0 → b = 1 := by decide
    exact hb _ (h.mpr hi)
  · simp only [hi, if_false]
    exact not_not.mp (fun hn => hi (h.mp hn))

theorem octadComplementWord_apply (O : Octad) (i : Omega) :
    (octadComplementWord O).val i = if i ∈ O.val then 0 else 1 := by
  classical
  change (1 : Bit) + (octadWord O).val i = _
  rw [octadWord_apply]
  split_ifs <;> decide

theorem octadComplementWord_mem (O : Octad) :
    octadComplementWord O ∈ octadShortenedCode O := by
  rw [mem_octadShortenedCode]
  intro i hi
  simp [octadComplementWord_apply, hi]

theorem octadComplementWord_ne_zero (O : Octad) : octadComplementWord O ≠ 0 := by
  intro h
  have hfull : O.val = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hi
    have he := congrArg (fun c : golay => c.val i) h
    simp [octadComplementWord_apply, hi] at he
  have hc := octad_size O.val O.prop
  rw [hfull] at hc
  norm_num [Omega, HexIndex, Tetrad] at hc

/-- The eighth coordinate follows from the Golay/octad orthogonality equation. -/
theorem octadShortenedCode_eq_erased_kernel (O : Octad) (a : Omega) (ha : a ∈ O.val) :
    octadShortenedCode O = (golayRestriction (O.val.erase a)).ker := by
  ext c
  rw [mem_octadShortenedCode]
  change (∀ i ∈ O.val, c.val i = 0) ↔ golayRestriction (O.val.erase a) c = 0
  constructor
  · intro h
    funext i
    exact h i.val (Finset.mem_erase.mp i.prop).2
  · intro h
    have hz (i : Omega) (hi : i ∈ O.val.erase a) : c.val i = 0 :=
      congrFun h ⟨i,hi⟩
    have ho := golay_selfOrthogonal (octadWord O).prop c.val c.prop
    change binaryDot c.val (octadWord O).val = 0 at ho
    have he : (octadWord O).val = supportWord O.val := by
      funext i
      rw [octadWord_apply]
      rfl
    rw [he, tetradSignParity_dot, tetradSignParity, Finset.sum_coe_sort,
      ← Finset.add_sum_erase _ _ ha] at ho
    have hsum : (∑ i ∈ O.val.erase a, c.val i) = 0 := Finset.sum_eq_zero hz
    rw [hsum, add_zero] at ho
    intro i hi
    by_cases hia : i = a
    · simpa [hia] using ho
    · exact hz i (Finset.mem_erase.mpr ⟨hia,hi⟩)

theorem octadShortenedCode_finrank (O : Octad) :
    Module.finrank Bit (octadShortenedCode O) = 5 := by
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < O.val.card by
    rw [octad_size O.val O.prop]; decide)
  have hc : (O.val.erase a).card = 7 := by
    rw [Finset.card_erase_of_mem ha, octad_size O.val O.prop]
  have hs := golay_small_restriction_surjective (O.val.erase a) (by omega)
  have he := (golayRestriction (O.val.erase a)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe, hc, golay_finrank] at he
  rw [octadShortenedCode_eq_erased_kernel O a ha]
  omega

/-- The distinguished constant-one vector in the shortened code. -/
def octadShortenedOne (O : Octad) : octadShortenedCode O :=
  ⟨octadComplementWord O, octadComplementWord_mem O⟩

theorem octadShortenedOne_ne_zero (O : Octad) : octadShortenedOne O ≠ 0 := by
  intro h
  exact octadComplementWord_ne_zero O (congrArg Subtype.val h)

end Atlas.Fischer

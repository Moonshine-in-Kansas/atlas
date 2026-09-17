import Atlas.Fischer.OctadHyperplaneConvolution

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance localConvolutionHyperplaneFintype (O : Octad) : Fintype (OctadShortenedHyperplane O) := Fintype.ofFinite _

private theorem twice_word (O : Octad) (a : octadShortenedCode O) : a + a = 0 := by
  rw [← two_smul Bit, show (2 : Bit) = 0 from rfl, zero_smul]

abbrev OctadHyperplaneLocalDomain (O : Octad) (b : OctadShortenedHyperplane O) :=
  {c : OctadShortenedHyperplane O //
    b.val + c.val ≠ 0 ∧ b.val + c.val ≠ octadShortenedOne O}

def octadHyperplaneLocalSum (O : Octad) (b : OctadShortenedHyperplane O)
    (c : OctadHyperplaneLocalDomain O b) : OctadShortenedHyperplane O :=
  ⟨b.val + c.val.val, c.prop⟩

private theorem local_sum_admissible (O : Octad) (b c : OctadShortenedHyperplane O) :
    (b.val + c.val ≠ 0 ∧ b.val + c.val ≠ octadShortenedOne O) ↔
      c ≠ b ∧ c ≠ octadHyperplaneComplement O b := by
  have hz : b.val + c.val = 0 ↔ c = b := by
    constructor
    · intro h
      apply Subtype.ext
      have hh := congrArg (fun a : octadShortenedCode O => b.val + a) h
      simpa only [← add_assoc, twice_word, zero_add, add_zero] using hh
    · intro h
      rw [h, twice_word]
  have ho : b.val + c.val = octadShortenedOne O ↔
      c = octadHyperplaneComplement O b := by
    constructor
    · intro h
      apply Subtype.ext
      have hh := congrArg (fun a : octadShortenedCode O => b.val + a) h
      simpa only [← add_assoc, twice_word, zero_add, octadHyperplaneComplement] using hh
    · intro h
      rw [h]
      change b.val + (b.val + octadShortenedOne O) = octadShortenedOne O
      rw [← add_assoc, twice_word, zero_add]
  exact and_congr (not_congr hz) (not_congr ho)

def octadHyperplaneLocalEquiv (O : Octad) (b : OctadShortenedHyperplane O) :
    OctadHyperplaneLocalDomain O b ≃
      {d : OctadShortenedHyperplane O // d ≠ b ∧ d ≠ octadHyperplaneComplement O b} where
  toFun c := ⟨octadHyperplaneLocalSum O b c, by
    apply (local_sum_admissible O b _).mp
    change b.val + (b.val + c.val.val) ≠ 0 ∧
      b.val + (b.val + c.val.val) ≠ octadShortenedOne O
    rw [← add_assoc, twice_word, zero_add]
    exact c.val.prop⟩
  invFun d := ⟨⟨b.val + d.val.val, (local_sum_admissible O b d.val).mpr d.prop⟩, by
    change b.val + (b.val + d.val.val) ≠ 0 ∧
      b.val + (b.val + d.val.val) ≠ octadShortenedOne O
    rw [← add_assoc, twice_word, zero_add]
    exact d.val.prop⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    change b.val + (b.val + c.val.val) = c.val.val
    rw [← add_assoc, twice_word, zero_add]
  right_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    change b.val + (b.val + d.val.val) = d.val.val
    rw [← add_assoc, twice_word, zero_add]

/-- The local convolution omits precisely a hyperplane and its complement. -/
theorem octadHyperplane_local_convolution (O : Octad)
    (b : OctadShortenedHyperplane O) {M : Type*} [AddCommGroup M]
    (F : OctadShortenedHyperplane O → M) :
    (∑ c : OctadHyperplaneLocalDomain O b, F (octadHyperplaneLocalSum O b c)) =
      (∑ d : OctadShortenedHyperplane O, F d) - F b - F (octadHyperplaneComplement O b) := by
  classical
  change (∑ c, F ((octadHyperplaneLocalEquiv O b) c).val) = _
  rw [(octadHyperplaneLocalEquiv O b).sum_comp (fun d => F d.val)]
  have he : (∑ d : {d : OctadShortenedHyperplane O //
      d ≠ b ∧ d ≠ octadHyperplaneComplement O b}, F d.val) =
      ∑ d ∈ ({b, octadHyperplaneComplement O b}ᶜ : Finset _), F d := by
    symm
    apply Finset.sum_subtype
    intro d
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
  rw [he]
  have h := Finset.sum_compl_add_sum (s := {b, octadHyperplaneComplement O b}) F
  have hn : b ∉ ({octadHyperplaneComplement O b} : Finset _) := by
    simpa only [Finset.mem_singleton] using Ne.symm (octadHyperplaneComplement_ne O b)
  rw [Finset.sum_insert hn, Finset.sum_singleton] at h
  rw [sub_sub]
  exact eq_sub_iff_add_eq.mpr h

end Atlas.Fischer

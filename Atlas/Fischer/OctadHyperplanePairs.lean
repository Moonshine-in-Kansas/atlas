import Atlas.Fischer.OctadHyperplaneCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable
local instance (O : Octad) : Fintype (OctadShortenedHyperplane O) := Fintype.ofFinite _

private theorem shortened_add_self (O : Octad) (a : octadShortenedCode O) : a+a=0 := by
  rw [← two_smul Bit,show (2 : Bit) = 0 from rfl,zero_smul]

/-- Complementation inside the actual sixteen-point octad exterior. -/
def octadHyperplaneComplement (O : Octad) (c : OctadShortenedHyperplane O) :
    OctadShortenedHyperplane O :=
  ⟨c.val + octadShortenedOne O, ⟨by
    intro h
    apply c.prop.2
    have hh := congrArg (fun a : octadShortenedCode O => a+octadShortenedOne O) h
    simpa only [add_assoc,shortened_add_self,add_zero,zero_add] using hh,
    fun h => c.prop.1 (add_right_cancel (h.trans (zero_add _).symm))⟩⟩

theorem octadHyperplaneComplement_ne (O : Octad) (c : OctadShortenedHyperplane O) :
    octadHyperplaneComplement O c ≠ c := by
  intro h
  apply octadShortenedOne_ne_zero O
  have hh := congrArg Subtype.val h
  change c.val + octadShortenedOne O = c.val at hh
  exact add_left_cancel (hh.trans (add_zero _).symm)

theorem octadHyperplaneComplement_involutive (O : Octad) :
    Function.Involutive (octadHyperplaneComplement O) := by
  intro c
  apply Subtype.ext
  change (c.val+octadShortenedOne O)+octadShortenedOne O=c.val
  rw [add_assoc,shortened_add_self,add_zero]

private theorem hyperplane_sum_zero (O : Octad) (b c : OctadShortenedHyperplane O) :
    b.val+c.val=0 ↔ b=c := by
  constructor
  · intro h
    apply Subtype.ext
    have hh := congrArg (fun a : octadShortenedCode O => a+c.val) h
    simpa only [add_assoc,shortened_add_self,add_zero,zero_add] using hh
  · intro h
    rw [h]
    exact shortened_add_self O c.val

private theorem hyperplane_sum_one (O : Octad) (b c : OctadShortenedHyperplane O) :
    b.val+c.val=octadShortenedOne O ↔ b=octadHyperplaneComplement O c := by
  constructor
  · intro h
    apply Subtype.ext
    have hh := congrArg (fun a : octadShortenedCode O => a+c.val) h
    simpa only [add_assoc,shortened_add_self,add_zero,octadHyperplaneComplement,
      add_comm (octadShortenedOne O) c.val] using hh
  · intro h
    subst b
    change (c.val+octadShortenedOne O)+c.val=octadShortenedOne O
    rw [add_right_comm,shortened_add_self,zero_add]

/-- For every fixed hyperplane c, exactly 28 actual hyperplanes b have b+c
again a nonzero nonconstant shortened word. -/
theorem octadShortenedHyperplane_sum_card (O : Octad) (c : OctadShortenedHyperplane O) :
    Fintype.card {b : OctadShortenedHyperplane O //
      b.val+c.val ≠ 0 ∧ b.val+c.val ≠ octadShortenedOne O} = 28 := by
  classical
  have h := Fintype.card_of_subtype
    ({c,octadHyperplaneComplement O c}ᶜ : Finset (OctadShortenedHyperplane O))
    (p := fun b => b.val+c.val ≠ 0 ∧ b.val+c.val ≠ octadShortenedOne O)
    (by
      intro b
      simp only [Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton,not_or]
      exact and_congr (not_congr (hyperplane_sum_zero O b c).symm)
        (not_congr (hyperplane_sum_one O b c).symm))
  have hn := octadShortenedHyperplane_natCard O
  have hc : Fintype.card (OctadShortenedHyperplane O) = 30 :=
    Nat.card_eq_fintype_card.symm.trans hn
  rw [h,Finset.card_compl,hc]
  simp [Ne.symm (octadHyperplaneComplement_ne O c)]

end Atlas.Fischer

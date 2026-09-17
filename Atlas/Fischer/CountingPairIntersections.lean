import Atlas.Fischer.CountingFieldTrace

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

/-- A source Type B column: a line through zero, or its complementary pair. -/
def countingColumnPair (g : CountingFour) (e : Bit) : Finset CountingFour :=
  if g=0 then ∅ else if e=0 then {0,g} else Finset.univ \ {0,g}

/-- A source Type C column: a singleton, or its complementary triple. -/
def countingColumnSingleton (h : CountingFour) (distinguished : Bool) : Finset CountingFour :=
  if distinguished then Finset.univ \ {h} else {h}

/-- Source pair-intersection-rule, including the zero-support columns. -/
theorem countingColumnPair_intersection (g h : CountingFour) (e : Bit) :
    ((countingColumnPair g 0) ∩ countingColumnPair h e).card =
      if g=0 ∨ h=0 then 0 else if g=h then (if e=0 then 2 else 0) else 1 := by
  revert g h e
  decide

/-- The local Type B/Type C rule, for every field letter and either target column. -/
theorem countingColumnPair_singleton_intersection (g h : CountingFour) (d : Bool) :
    ((countingColumnPair g 0) ∩ countingColumnSingleton h d).card =
      if g=0 then 0 else if d then 1+(countingFieldTrace (h/g)).val
      else 1-(countingFieldTrace (h/g)).val := by
  simp only [countingFour_div]
  revert g h d
  decide

/-- Translation changes a pair precisely by the absolute trace of its displacement. -/
theorem countingColumnPair_translation (g b z : CountingFour) (e : Bit) :
    z+b ∈ countingColumnPair g e ↔
      z ∈ countingColumnPair g (e+countingFieldTrace (b/g)) := by
  simp only [countingFour_div]
  revert g b z e
  decide

theorem countingColumnSingleton_translation (h b z : CountingFour) (d : Bool) :
    z+b ∈ countingColumnSingleton h d ↔
      z ∈ countingColumnSingleton (h+b) d := by
  revert h b z d
  decide

end Atlas.Fischer

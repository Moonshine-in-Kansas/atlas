import Atlas.Codes.TernaryGolaySupports

namespace Atlas.Codes

theorem ternarySix_not_constant (c : TernarySixWords) (a : ZMod 3) :
    ¬(∀ i,c.val.val i=a) := by
  intro ha
  have he : c.val.val=(fun _ => a) := funext ha
  have hc := c.property
  rw [he] at hc
  by_cases hz : a=0 <;> simp [ternaryWeight,hz] at hc

/-- A nonconstant weight-six word cannot equal its negative modulo constant words. -/
theorem ternarySix_not_negative_shift (c : TernarySixWords) (a : ZMod 3) :
    ¬(∀ i,c.val.val i-(-c.val.val i)=a) := by
  intro h
  have hf : ∀ x y : ZMod 3,x-(-x)=y → x= -y := by decide +kernel
  exact ternarySix_not_constant c (-a) (fun i => hf _ _ (h i))

end Atlas.Codes

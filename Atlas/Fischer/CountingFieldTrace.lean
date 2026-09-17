import Atlas.Fischer.CountingHexacodeField

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

/-- The absolute F4/F2 trace in the retained basis 1,tau. -/
def countingFieldTrace (z : CountingFour) : Bit := z.im

theorem countingFieldTrace_add (x y : CountingFour) :
    countingFieldTrace (x+y)=countingFieldTrace x+countingFieldTrace y := rfl

theorem countingFieldTrace_frobenius (z : CountingFour) :
    (algebraMap Bit CountingFour (countingFieldTrace z))=z+z^2 := by
  revert z
  decide

theorem countingFieldTrace_zero_iff (z : CountingFour) :
    countingFieldTrace z=0 ↔ z=0 ∨ z=1 := by
  revert z
  decide

theorem countingFour_inv (g : CountingFour) : g⁻¹=g^2 := by
  by_cases hg : g=0
  · simp [hg]
  · have hm : ∀ a : CountingFour, a ≠ 0 → a*a^2=1 := by decide
    calc
      g⁻¹=g⁻¹*(g*g^2) := by rw [hm g hg,mul_one]
      _=g^2 := by rw [← mul_assoc,inv_mul_cancel₀ hg,one_mul]

theorem countingFour_div (x y : CountingFour) : x/y=x*y^2 := by
  rw [div_eq_mul_inv,countingFour_inv]

theorem countingFieldTrace_pair (g z : CountingFour) (hg : g ≠ 0) :
    countingFieldTrace (z/g)=0 ↔ z=0 ∨ z=g := by
  simp only [countingFour_div]
  revert g z
  decide

theorem countingFieldTrace_ratio (g z : CountingFour) (hg : g ≠ 0) :
    countingFieldTrace (z/g)=countingFieldTrace (z*g^2) := by
  rw [countingFour_div]

theorem countingFieldTrace_bit (z : CountingFour) :
    countingFieldTrace z=0 ∨ countingFieldTrace z=1 := by
  revert z
  decide

end Atlas.Fischer

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Module.Basic

/-! A small obstruction for inconsistent additive tables in characteristic two. -/
namespace Atlas
variable {F V W : Type*} [CommRing F] [CharP F 2]
  [AddCommGroup V] [AddCommGroup W] [Module F W]

include F in
theorem charTwo_equal_values_of_sum_force_zero (f : V →+ W)
    (a b c : V) (z : W) (hab : a+b=c)
    (ha : f a=z) (hb : f b=z) (hc : f c=z) : z=0 := by
  have h : z+z=z := by
    calc z+z = f a + f b := by rw [ha, hb]
         _ = f (a+b) := (f.map_add a b).symm
         _ = z := by rw [hab, hc]
  have hz : z+z=0 := by
    rw [← two_smul F, (CharTwo.two_eq_zero (R:=F)), zero_smul]
  exact h.symm.trans hz

end Atlas

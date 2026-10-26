import Atlas.LinearGroups.F4.SimpleCorootDefinitions
import Atlas.LinearGroups.F4.ShortRootPairTwo

noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

private theorem map_vec4 {A B : Type*} (f : A → B) (a b c d : A) (j : Fin 4) :
    f (![a,b,c,d] j) = ![f a,f b,f c,f d] j := by
  fin_cases j <;> rfl

private theorem shortRoot_pair_zero_apply (i : Fin 8) (t : F) (x : Atlas.Albert.Carrier F) :
    (shortRoot 0 i t).val x = Atlas.Albert.shortRootLinear i t x := by
  have h : shortRoot 0 i t = shortRootFirstPair i t := by simp [shortRoot]
  exact (congrArg (fun g : Model F => g.val x) h).trans (shortRootFirstPair_apply i t x)

attribute [local irreducible] longRoot simplePositive simpleNegative

theorem simplePositive_apply (j : Fin 4) (t : F) (x : Atlas.Albert.Carrier F) :
    (simplePositive j t).val x = simplePositiveApply j t x := by
  have h := map_vec4 (fun g : Model F => g.val x)
    (longRoot (torusLongLabel 0) t) (longRoot (torusLongLabel 2) t)
    (shortRoot 0 3 t) (shortRoot 2 3 t) j
  rw [longRoot_torusLongApply, longRoot_torusLongApply,
    shortRoot_pair_zero_apply, shortRoot_pair_two_apply] at h
  simpa only [simplePositive, simplePositiveApply] using h

theorem simpleNegative_apply (j : Fin 4) (t : F) (x : Atlas.Albert.Carrier F) :
    (simpleNegative j t).val x = simpleNegativeApply j t x := by
  have h := map_vec4 (fun g : Model F => g.val x)
    (longRoot (torusLongLabel 1) t) (longRoot (torusLongLabel 3) t)
    (shortRoot 0 4 t) (shortRoot 2 4 t) j
  rw [longRoot_torusLongApply, longRoot_torusLongApply,
    shortRoot_pair_zero_apply, shortRoot_pair_two_apply] at h
  simpa only [simpleNegative, simpleNegativeApply] using h

end Atlas.F4

import Atlas.Rudvalis.HeavyCommonPerpendicular
import Atlas.Rudvalis.SelectedCoordinateRows

namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary
local instance : DecidablePred HeavyCoupleLabel := fun c =>
  inferInstanceAs (Decidable (c.val=binaryLabel 2 ∨ c.val=binaryLabel 4))
local instance : DecidablePred (fun p : Point => p∈referenceDozenRows) :=
  fun p => inferInstanceAs (Decidable (dot (binaryLabel 1) p.val=0))

theorem fixedHeavyWord_row_weight (c p : Point) (v : FixedHeavyParameters c) :
    hammingNorm (fun x => fixedHeavyWord c v (p,x))=if p=c then 4 else 2 := by
  have h := (binaryNormalMap_quadratic_weight_sixteen (v.2.val,v.1.val,c.val) c.prop).mp v.2.prop p
  have he : (fun x => fixedHeavyWord c v (p,x))=
      (fun x => v.2.val p+dot (matrixAt v.1.val p.val+eta p c.val) x+quadratic c.val x) := by
    funext x
    exact fixedHeavyWord_row_quadratic c v p x
  rw [he]
  simpa only [blockWeight,Subtype.val_inj] using h

theorem heavyCouple_selected_row_weight (c : Point) (hc : HeavyCoupleLabel c)
    (v : FixedHeavyParameters c) :
    (∑p ∈ Finset.univ.filter (fun p : Point => p∈referenceDozenRows),
      hammingNorm (fun x => fixedHeavyWord c v (p,x)))=8 := by
  simp_rw [fixedHeavyWord_row_weight]
  have h : ∀c : Point, HeavyCoupleLabel c →
      (∑p ∈ Finset.univ.filter (fun p : Point => p∈referenceDozenRows),
        if p=c then (4 : ℕ) else 2)=8 := by
    decide +kernel
  exact h c hc

theorem minimumWord_integerLift_row_square (w : MinimumWords) (p : Point) :
    (∑x : E,integerLift w.val.val (p,x)^2)=
      (hammingNorm (fun x => reduce w.val.val (p,x)) : ℤ) := by
  have hs : ∀ a : Quat,a≠2 → integerRepresentative a^2=
      if reduceScalar a=0 then (0 : ℤ) else 1 := by decide +kernel
  have ht := quaternary_minimum_no_twos w.val.val w.val.prop w.prop
  simp only [integerLift,hs _ (ht _),hammingNorm,Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [reduce,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  split_ifs <;> simp_all

theorem heavyCouple_integerLift_selected_square (w : HeavyCoupleWords) :
    (∑p ∈ Finset.univ.filter (fun p : Point => p∈referenceDozenRows),
      ∑x : E,integerLift w.val.val.val (p,x)^2)=8 := by
  let z := heavyCoupleResidueEquiv.symm
    ⟨⟨⟨reduce w.val.val.val,(quaternaryCode_residue _).mpr ⟨w.val.val.val,w.val.val.prop,rfl⟩⟩,
      w.val.prop.2,quaternary_minimum_residue_weight _ w.val.val.prop w.val.prop.1⟩,w.prop⟩
  have hr : fixedHeavyWord z.1 z.2.val.val=reduce w.val.val.val :=
    congrArg (fun a : HeavyCoupleResidues => a.val.val.val)
      (heavyCoupleResidueEquiv.apply_symm_apply _)
  have hc := (heavy_couple_second_pair_iff z.1 z.2.val).mp z.2.prop
  have hh := heavyCouple_selected_row_weight z.1 hc z.2.val.val
  rw [hr] at hh
  have he : (∑p ∈ Finset.univ.filter (fun p : Point => p∈referenceDozenRows),
      ∑x : E,integerLift w.val.val.val (p,x)^2)=
      ∑p ∈ Finset.univ.filter (fun p : Point => p∈referenceDozenRows),
        (hammingNorm (fun x => reduce w.val.val.val (p,x)) : ℤ) := by
    apply Finset.sum_congr rfl
    intro p _
    exact minimumWord_integerLift_row_square (heavyMinimumWord w.val) p
  rw [he]
  exact_mod_cast hh

end Atlas.Rudvalis

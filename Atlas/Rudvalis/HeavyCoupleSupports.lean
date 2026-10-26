import Atlas.Rudvalis.HeavyCoordinateStabilizerOrbit

/-! Heavy supports avoiding the reference four-position plane have labels 2 or 4. -/
namespace Atlas.Rudvalis
open scoped BigOperators
local instance : DecidableEq E := Fintype.decidablePiFintype

theorem fixedHeavyWord_row_period (c p : Point) (hpc : p≠c) (v : FixedHeavyParameters c) (y : E) :
    fixedHeavyWord c v (p,y+c.val)=fixedHeavyWord c v (p,y) := by
  obtain ⟨u,huc,hup⟩ := independent_point_functional c p hpc
  have h := congrFun (fixedHeavy_outer_stabilizes c v u huc) (p,y)
  change fixedHeavyWord c v (p,y+matrixAt (outerMatrix c.val u) p.val)=_ at h
  rw [matrixAt_outer,hup,one_smul] at h
  exact h

def HeavyCoupleLabel (c : Point) : Prop := c.val=binaryLabel 2 ∨ c.val=binaryLabel 4

local instance : DecidablePred HeavyCoupleLabel := fun c => inferInstanceAs (Decidable (c.val=binaryLabel 2 ∨ c.val=binaryLabel 4))

theorem heavyCoupleLabel_card : Nat.card {c : Point // HeavyCoupleLabel c}=2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem heavyCoupleLabel_ne (c : Point) (hc : HeavyCoupleLabel c) : rowLabel 0≠c := by
  decide +kernel +revert

theorem heavy_couple_second_pair_iff (c : Point) (v : HeavyAvoidingPair c (rowLabel 0) 0) :
    (fixedHeavyWord c v.val (rowLabel 0,binaryLabel 2)=0 ∧
      fixedHeavyWord c v.val (rowLabel 0,binaryLabel 2+(rowLabel 0).val)=0) ↔ HeavyCoupleLabel c := by
  have hpc := heavyAvoidingPair_label_ne c (rowLabel 0) v
  constructor
  · rintro ⟨h2,h4⟩
    have h := heavy_pair_translation_value c (rowLabel 0) hpc v
      (rowTranslationMatrix (rowLabel 0) (binaryLabel 2))
      (by rw [rowTranslationMatrix_at];exact h2)
      (by rw [rowTranslationMatrix_at];simpa only [add_comm] using h4)
    rw [rowTranslationMatrix_at] at h
    have hi : ∀c : Point,
        binaryLabel 2=0 ∨ binaryLabel 2=(rowLabel 0).val ∨ binaryLabel 2=c.val ∨
        binaryLabel 2=(rowLabel 0).val+c.val → HeavyCoupleLabel c := by
      decide +kernel
    exact hi c h
  · intro hc
    have h0 := v.prop.1
    have h6 : fixedHeavyWord c v.val (rowLabel 0,(rowLabel 0).val)=0 := by
      simpa only [zero_add] using v.prop.2
    rcases hc with hc|hc
    · have h2 := fixedHeavyWord_row_period c (rowLabel 0) hpc v.val 0
      have h4 := fixedHeavyWord_row_period c (rowLabel 0) hpc v.val (rowLabel 0).val
      exact ⟨by simpa only [hc,zero_add] using h2.trans h0,
        by simpa only [hc,add_comm] using h4.trans h6⟩
    · have h4 := fixedHeavyWord_row_period c (rowLabel 0) hpc v.val 0
      have h2 := fixedHeavyWord_row_period c (rowLabel 0) hpc v.val (rowLabel 0).val
      have h24 : binaryLabel 2+(rowLabel 0).val=binaryLabel 4 := by decide
      have h62 : (rowLabel 0).val+binaryLabel 4=binaryLabel 2 := by decide
      exact ⟨by simpa only [hc,h62] using h2.trans h6,
        by simpa only [hc,zero_add,h24] using h4.trans h0⟩

abbrev HeavyCoupleParameters := Σ c : Point,
  {v : HeavyAvoidingPair c (rowLabel 0) 0 //
    fixedHeavyWord c v.val (rowLabel 0,binaryLabel 2)=0 ∧
    fixedHeavyWord c v.val (rowLabel 0,binaryLabel 2+(rowLabel 0).val)=0}

noncomputable def heavyCoupleParametersEquiv : HeavyCoupleParameters ≃
    Σ c : {c : Point // HeavyCoupleLabel c},HeavyAvoidingPair c.val (rowLabel 0) 0 where
  toFun z := ⟨⟨z.1,(heavy_couple_second_pair_iff z.1 z.2.val).mp z.2.prop⟩,z.2.val⟩
  invFun z := ⟨z.1.val,⟨z.2,(heavy_couple_second_pair_iff z.1.val z.2).mpr z.1.prop⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem heavyCoupleParameters_card : Nat.card HeavyCoupleParameters=128 := by
  classical
  rw [Nat.card_congr heavyCoupleParametersEquiv,Nat.card_sigma]
  have h (c : {c : Point // HeavyCoupleLabel c}) :
      Nat.card (HeavyAvoidingPair c.val (rowLabel 0) 0)=64 := by
    rw [heavyAvoidingPair_card,ite_eq_right (heavyCoupleLabel_ne c.val c.prop)]
  simp_rw [h]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,heavyCoupleLabel_card]

end Atlas.Rudvalis

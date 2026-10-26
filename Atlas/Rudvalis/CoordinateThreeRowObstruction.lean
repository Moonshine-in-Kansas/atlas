import Atlas.Rudvalis.HeavyCoordinateTests
import Atlas.Rudvalis.CoordinateCrossAction

namespace Atlas.Rudvalis

set_option synthInstance.maxSize 8192 in
set_option maxSynthPendingDepth 256 in
set_option maxHeartbeats 3000000 in
theorem heavy_label_avoiding_three_rows (p q r : Point) (d : E) (hd0 : d≠0) (hdp : d≠p.val) :
    ∃c : Point,p≠c ∧ q≠c ∧ r≠c ∧ d≠c.val ∧ d≠c.val+p.val := by
  decide +kernel +revert

/-- A genuine heavy cross detects a single member of the doubled row while avoiding two singleton rows. -/
theorem heavy_two_one_one_test (p q r : Point) (hqr : q≠r) (x y z t : E)
    (hxy : coordinateCross (p,x)≠coordinateCross (p,y)) :
    ∃v : MinimalCross,v∉coordinateFrame ∧
      (CrossOrthogonal v (coordinateCross (p,x)) ↔ ¬CrossOrthogonal v (coordinateCross (p,y))) ∧
      CrossOrthogonal v (coordinateCross (q,z)) ∧ CrossOrthogonal v (coordinateCross (r,t)) := by
  have hd0 : y+x≠0 := by
    intro h
    have he : y=x := by
      calc y=(y+x)+x := by rw [add_assoc,vector_add_self,add_zero]
           _=x := by rw [h,zero_add]
    exact hxy (by rw [he])
  have hdp : y+x≠p.val := by
    intro h
    have he : y=x+p.val := by
      calc y=(y+x)+x := by rw [add_assoc,vector_add_self,add_zero]
           _=x+p.val := by rw [h,add_comm]
    apply hxy
    rw [he]
    simpa only [codeI_coordinate] using (coordinateCross_I (p,x)).symm
  obtain ⟨c,hpc,hqc,hrc,hdc,hdcp⟩ := heavy_label_avoiding_three_rows p q r (y+x) hd0 hdp
  have hn : Nonempty (FixedHeavyParameters c) :=
    (Nat.card_pos_iff.mp (show 0<Nat.card (FixedHeavyParameters c) by rw [fixedHeavyParameters_card]; decide)).1
  obtain ⟨v⟩ := hn
  obtain ⟨bq,hbq⟩ := fixedHeavy_pair_avoid_translate q c hqc v z
  obtain ⟨br,hbr⟩ := fixedHeavy_pair_avoid_translate r c hrc v t
  obtain ⟨B,hBq,hBr⟩ := matrixAt_two_points q r hqr bq br
  let v' := fixedHeavyTranslate c B v
  obtain ⟨w,hw,ht⟩ := fixedHeavy_test_cross c v'
  refine ⟨w,hw,?_,?_,?_⟩
  · rw [ht p x,ht p y]
    have h := fixedHeavy_pair_complement p c hpc (y+x) hd0 hdp hdc hdcp v' x
    have he : x+(y+x)=y := by rw [add_comm y x,←add_assoc,vector_add_self,zero_add]
    rwa [he] at h
  · rw [ht q z]
    change fixedHeavyWord c (fixedHeavyTranslate c B v) (q,z)=0 ∧ fixedHeavyWord c (fixedHeavyTranslate c B v) (q,z+q.val)=0
    rw [fixedHeavyTranslate_word]
    change fixedHeavyWord c v (q,z+matrixAt B q.val)=0 ∧ fixedHeavyWord c v (q,z+q.val+matrixAt B q.val)=0
    rwa [hBq]
  · rw [ht r t]
    change fixedHeavyWord c (fixedHeavyTranslate c B v) (r,t)=0 ∧ fixedHeavyWord c (fixedHeavyTranslate c B v) (r,t+r.val)=0
    rw [fixedHeavyTranslate_word]
    change fixedHeavyWord c v (r,t+matrixAt B r.val)=0 ∧ fixedHeavyWord c v (r,t+r.val+matrixAt B r.val)=0
    rwa [hBr]

/-- The forbidden (2,1,1) row pattern. -/
theorem coordinateQuartet_not_two_one_one (p q r : Point) (hqr : q≠r) (x y z t : E)
    (hxy : coordinateCross (p,x)≠coordinateCross (p,y))
    (Q : Set MinimalCross) (hQ : IsQuartet Q)
    (hx : coordinateCross (p,x)∈Q) (hy : coordinateCross (p,y)∈Q)
    (hrest : ∀u∈Q,u≠coordinateCross (p,x) → u≠coordinateCross (p,y) →
      u=coordinateCross (q,z) ∨ u=coordinateCross (r,t)) : False := by
  classical
  obtain ⟨v,hv,hpair,hq,hr⟩ := heavy_two_one_one_test p q r hqr x y z t hxy
  have hvQ : v∉Q := by
    intro h
    apply hv
    by_cases he : v=coordinateCross (p,x)
    · rw [he]; exact coordinateCross_mem _
    by_cases he' : v=coordinateCross (p,y)
    · rw [he']; exact coordinateCross_mem _
    rcases hrest v h he he' with h|h <;> rw [h] <;> exact coordinateCross_mem _
  by_cases ho : CrossOrthogonal v (coordinateCross (p,x))
  · apply (hpair.mp ho)
    apply hQ.2.2 v hvQ (coordinateCross (p,y)) hy
    intro u hu huy
    by_cases hux : u=coordinateCross (p,x)
    · rwa [hux]
    rcases hrest u hu hux huy with h|h <;> rw [h] <;> assumption
  · apply ho
    apply hQ.2.2 v hvQ (coordinateCross (p,x)) hx
    intro u hu hux
    by_cases huy : u=coordinateCross (p,y)
    · rw [huy]
      by_contra hny
      exact ho (hpair.mpr hny)
    rcases hrest u hu hux huy with h|h <;> rw [h] <;> assumption

end Atlas.Rudvalis

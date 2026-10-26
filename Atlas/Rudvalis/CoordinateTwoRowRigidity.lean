import Atlas.Rudvalis.CoordinateThreeRowObstruction

namespace Atlas.Rudvalis

set_option synthInstance.maxSize 2048 in
set_option maxSynthPendingDepth 256 in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
theorem quadratic_pair_radical_partner (p c : Point) (hpc : p≠c)
    (ε : Bit) (b x : E) (hw : blockWeight ε b c.val=2) :
    (ε+dot b x+quadratic c.val x=0 ∧ ε+dot b (x+p.val)+quadratic c.val (x+p.val)=0) ↔
      (ε+dot b (x+c.val)+quadratic c.val (x+c.val)=0 ∧
        ε+dot b (x+c.val+p.val)+quadratic c.val (x+c.val+p.val)=0) := by
  decide +kernel +revert

theorem fixedHeavy_pair_radical_partner (p c : Point) (hpc : p≠c)
    (v : FixedHeavyParameters c) (x : E) :
    (fixedHeavyWord c v (p,x)=0 ∧ fixedHeavyWord c v (p,x+p.val)=0) ↔
      (fixedHeavyWord c v (p,x+c.val)=0 ∧ fixedHeavyWord c v (p,x+c.val+p.val)=0) := by
  have hw := (binaryNormalMap_quadratic_weight_sixteen (v.2.val,v.1.val,c.val) c.prop).mp v.2.prop p
  have hn : p.val≠c.val := fun h => hpc (Subtype.ext h)
  simp only [hn,ite_false] at hw
  simp_rw [fixedHeavyWord_row_quadratic]
  exact quadratic_pair_radical_partner p c hpc _ _ x hw

theorem heavy_two_two_test (p q c : Point) (hpq : p≠q) (hpc : p≠c) (hqc : q≠c)
    (x y z t : E) (hxy : coordinateCross (p,x)≠coordinateCross (p,y))
    (hdy : y+x≠c.val) (hdyp : y+x≠c.val+p.val)
    (ht : t=z+c.val ∨ t=z+c.val+q.val) :
    ∃v : MinimalCross,v∉coordinateFrame ∧
      (CrossOrthogonal v (coordinateCross (p,x)) ↔ ¬CrossOrthogonal v (coordinateCross (p,y))) ∧
      CrossOrthogonal v (coordinateCross (q,z)) ∧ CrossOrthogonal v (coordinateCross (q,t)) := by
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
  have hn : Nonempty (FixedHeavyParameters c) :=
    (Nat.card_pos_iff.mp (show 0<Nat.card (FixedHeavyParameters c) by rw [fixedHeavyParameters_card]; decide)).1
  obtain ⟨v⟩ := hn
  obtain ⟨bq,hbq⟩ := fixedHeavy_pair_avoid_translate q c hqc v z
  obtain ⟨B,_,hBq⟩ := matrixAt_two_points p q hpq 0 bq
  let v' := fixedHeavyTranslate c B v
  obtain ⟨w,hw,hwtest⟩ := fixedHeavy_test_cross c v'
  have hz : fixedHeavyWord c v' (q,z)=0 ∧ fixedHeavyWord c v' (q,z+q.val)=0 := by
    change fixedHeavyWord c (fixedHeavyTranslate c B v) (q,z)=0 ∧ fixedHeavyWord c (fixedHeavyTranslate c B v) (q,z+q.val)=0
    rw [fixedHeavyTranslate_word]
    change fixedHeavyWord c v (q,z+matrixAt B q.val)=0 ∧ fixedHeavyWord c v (q,z+q.val+matrixAt B q.val)=0
    rwa [hBq]
  refine ⟨w,hw,?_,(hwtest q z).mpr hz,?_⟩
  · rw [hwtest p x,hwtest p y]
    have h := fixedHeavy_pair_complement p c hpc (y+x) hd0 hdp hdy hdyp v' x
    have he : x+(y+x)=y := by rw [add_comm y x,←add_assoc,vector_add_self,zero_add]
    rwa [he] at h
  · have hzc := (fixedHeavy_pair_radical_partner q c hqc v' z).mp hz
    rcases ht with rfl|rfl
    · exact (hwtest q _).mpr hzc
    · apply (hwtest q _).mpr
      have he : z+c.val+q.val+q.val=z+c.val := by rw [add_assoc,vector_add_self,add_zero]
      rw [he]
      exact ⟨hzc.2,hzc.1⟩

/-- Any external test cross with exactly one supported member contradicts quartet closure. -/
theorem quartet_pair_test_obstruction (Q : Set MinimalCross) (hQ : IsQuartet Q)
    (u v a b w : MinimalCross) (hu : u∈Q) (hv : v∈Q) (hw : w∉Q)
    (hpair : CrossOrthogonal w u ↔ ¬CrossOrthogonal w v)
    (ha : CrossOrthogonal w a) (hb : CrossOrthogonal w b)
    (hrest : ∀z∈Q,z≠u → z≠v → z=a ∨ z=b) : False := by
  classical
  by_cases ho : CrossOrthogonal w u
  · apply hpair.mp ho
    apply hQ.2.2 w hw v hv
    intro z hz hzv
    by_cases hzu : z=u
    · rwa [hzu]
    rcases hrest z hz hzu hzv with h|h <;> rw [h] <;> assumption
  · apply ho
    apply hQ.2.2 w hw u hu
    intro z hz hzu
    by_cases hzv : z=v
    · rw [hzv]
      by_contra hnv
      exact ho (hpair.mpr hnv)
    rcases hrest z hz hzu hzv with h|h <;> rw [h] <;> assumption

theorem coordinateQuartet_two_row_direction_imp (p q c : Point)
    (hpq : p≠q) (hpc : p≠c) (hqc : q≠c) (x y z t : E)
    (hxy : coordinateCross (p,x)≠coordinateCross (p,y))
    (hQ : IsQuartet {coordinateCross (p,x),coordinateCross (p,y),coordinateCross (q,z),coordinateCross (q,t)})
    (hdir : t+z=c.val ∨ t+z=c.val+q.val) : y+x=c.val ∨ y+x=c.val+p.val := by
  classical
  by_contra hn
  push Not at hn
  have ht : t=z+c.val ∨ t=z+c.val+q.val := by
    rcases hdir with h|h
    · left
      calc t=(t+z)+z := by rw [add_assoc,vector_add_self,add_zero]
           _=z+c.val := by rw [h,add_comm]
    · right
      calc t=(t+z)+z := by rw [add_assoc,vector_add_self,add_zero]
           _=z+c.val+q.val := by rw [h]; abel
  obtain ⟨w,hw,hpair,hz,ht⟩ := heavy_two_two_test p q c hpq hpc hqc x y z t hxy hn.1 hn.2 ht
  apply quartet_pair_test_obstruction _ hQ (coordinateCross (p,x)) (coordinateCross (p,y))
    (coordinateCross (q,z)) (coordinateCross (q,t)) w (by simp) (by simp) ?_ hpair hz ht
  · intro u hu hux huy
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu
    rcases hu with h|h|h|h
    · exact False.elim (hux h)
    · exact False.elim (huy h)
    · exact Or.inl h
    · exact Or.inr h
  · intro h
    apply hw
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
    rcases h with h|h|h|h <;> rw [h] <;> exact coordinateCross_mem _

set_option synthInstance.maxSize 8192 in
set_option maxSynthPendingDepth 256 in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
theorem two_row_direction_rigidity (p q : Point) (hpq : p≠q) (d e : E)
    (hd0 : d≠0) (hdp : d≠p.val) (he0 : e≠0) (heq : e≠q.val)
    (h : ∀c : Point,p≠c → q≠c → (d=c.val ∨ d=c.val+p.val ↔ e=c.val ∨ e=c.val+q.val)) :
    (d=q.val ∨ d=q.val+p.val) ∧ (e=p.val ∨ e=p.val+q.val) := by
  decide +kernel +revert

theorem coordinateCross_difference_ne (p : Point) (x y : E)
    (hxy : coordinateCross (p,x)≠coordinateCross (p,y)) : y+x≠0 ∧ y+x≠p.val := by
  constructor
  · intro h
    have he : y=x := by
      calc y=(y+x)+x := by rw [add_assoc,vector_add_self,add_zero]
           _=x := by rw [h,zero_add]
    exact hxy (by rw [he])
  · intro h
    have he : y=x+p.val := by
      calc y=(y+x)+x := by rw [add_assoc,vector_add_self,add_zero]
           _=x+p.val := by rw [h,add_comm]
    apply hxy
    rw [he]
    simpa only [codeI_coordinate] using (coordinateCross_I (p,x)).symm

/-- The (2,2) row pattern forces the manuscript affine-plane directions. -/
theorem coordinateQuartet_two_row_rigidity (p q : Point) (hpq : p≠q) (x y z t : E)
    (hxy : coordinateCross (p,x)≠coordinateCross (p,y))
    (hzt : coordinateCross (q,z)≠coordinateCross (q,t))
    (hQ : IsQuartet {coordinateCross (p,x),coordinateCross (p,y),coordinateCross (q,z),coordinateCross (q,t)}) :
    (y+x=q.val ∨ y+x=q.val+p.val) ∧ (t+z=p.val ∨ t+z=p.val+q.val) := by
  have hd := coordinateCross_difference_ne p x y hxy
  have he := coordinateCross_difference_ne q z t hzt
  apply two_row_direction_rigidity p q hpq (y+x) (t+z) hd.1 hd.2 he.1 he.2
  intro c hpc hqc
  constructor
  · apply coordinateQuartet_two_row_direction_imp q p c hpq.symm hqc hpc z t x y hzt
    have hs : ({coordinateCross (q,z),coordinateCross (q,t),coordinateCross (p,x),coordinateCross (p,y)} : Set MinimalCross)=
        {coordinateCross (p,x),coordinateCross (p,y),coordinateCross (q,z),coordinateCross (q,t)} := by
      ext v
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    rwa [hs]
  · exact coordinateQuartet_two_row_direction_imp p q c hpq hpc hqc x y z t hxy hQ

end Atlas.Rudvalis

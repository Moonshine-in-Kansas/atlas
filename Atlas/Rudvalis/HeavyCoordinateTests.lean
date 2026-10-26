import Atlas.Rudvalis.CoordinateQuartetObstructions
import Atlas.Rudvalis.HeavyPairTranslation

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

/-- Any genuine heavy residue is witnessed by an actual noncoordinate minimum cross. -/
theorem fixedHeavy_test_cross (c : Point) (v : FixedHeavyParameters c) :
    ∃z : MinimalCross,z∉coordinateFrame ∧ ∀p : Point,∀x : E,
      CrossOrthogonal z (coordinateCross (p,x)) ↔
        fixedHeavyWord c v (p,x)=0 ∧ fixedHeavyWord c v (p,x+p.val)=0 := by
  have hd : hasNonzeroQuadraticPart (fixedHeavyWord c v) := ⟨(v.2.val,v.1.val,c.val),c.prop,rfl⟩
  have hc : Nat.card (minimumLift (fixedHeavyWord c v))=16 := heavy_minimum_fibre_card _ hd v.2.prop
  obtain ⟨w⟩ := (Nat.card_pos_iff.mp (show 0<Nat.card (minimumLift (fixedHeavyWord c v)) by rw [hc]; decide)).1
  let w' : MinimumWords := ⟨w.val,w.prop.1⟩
  refine ⟨minimalCross (minimumWordShellLift w'),?_,?_⟩
  · intro h
    obtain ⟨i,hi⟩ := (minimalCross_mem_coordinateFrame _).mp h
    exact coordinateShellLift_ne_minimumWordShellLift i w' hi
  · intro p x
    rw [crossOrthogonal_symm,coordinateCross,crossOrthogonal_mk]
    change HermitianOrthogonal (coordinateMinimum (p,x)) (minimumWordShellLift w').val.val ↔ _
    rw [coordinate_hermitianOrthogonal_pair,minimumWordShellLift_zero_iff,minimumWordShellLift_zero_iff]
    exact and_congr (congrFun w.prop.2 (p,x) ▸ Iff.rfl) (congrFun w.prop.2 (p,x+p.val) ▸ Iff.rfl)

set_option maxSynthPendingDepth 256 in
set_option synthInstance.maxSize 8192 in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
theorem quadratic_pair_complement (p c : Point) (hpc : p≠c) (d : E)
    (hd0 : d≠0) (hdp : d≠p.val) (hdc : d≠c.val) (hdcp : d≠c.val+p.val)
    (ε : Bit) (b x : E) (hw : blockWeight ε b c.val=2) :
    (ε+dot b x+quadratic c.val x=0 ∧ ε+dot b (x+p.val)+quadratic c.val (x+p.val)=0) ↔
      ¬(ε+dot b (x+d)+quadratic c.val (x+d)=0 ∧
        ε+dot b (x+d+p.val)+quadratic c.val (x+d+p.val)=0) := by
  decide +kernel +revert

theorem fixedHeavy_pair_complement (p c : Point) (hpc : p≠c) (d : E)
    (hd0 : d≠0) (hdp : d≠p.val) (hdc : d≠c.val) (hdcp : d≠c.val+p.val)
    (v : FixedHeavyParameters c) (x : E) :
    (fixedHeavyWord c v (p,x)=0 ∧ fixedHeavyWord c v (p,x+p.val)=0) ↔
      ¬(fixedHeavyWord c v (p,x+d)=0 ∧ fixedHeavyWord c v (p,x+d+p.val)=0) := by
  have hw := (binaryNormalMap_quadratic_weight_sixteen (v.2.val,v.1.val,c.val) c.prop).mp v.2.prop p
  have hn : p.val≠c.val := fun h => hpc (Subtype.ext h)
  simp only [hn,ite_false] at hw
  simp_rw [fixedHeavyWord_row_quadratic]
  exact quadratic_pair_complement p c hpc d hd0 hdp hdc hdcp _ _ x hw

theorem fixedHeavy_pair_avoid_translate (p c : Point) (hpc : p≠c) (v : FixedHeavyParameters c) (x : E) :
    ∃b : E,fixedHeavyWord c v (p,x+b)=0 ∧ fixedHeavyWord c v (p,x+p.val+b)=0 := by
  classical
  have hc := fixedHeavy_row_pairs_card c p v
  rw [ite_eq_right hpc] at hc
  have hn : (Finset.univ.filter (fun y : E => fixedHeavyWord c v (p,y)=0 ∧ fixedHeavyWord c v (p,y+p.val)=0)).Nonempty :=
    Finset.card_pos.mp (by rw [hc]; decide)
  obtain ⟨y,hy⟩ := hn
  have hy := (Finset.mem_filter.mp hy).2
  refine ⟨y+x,?_,?_⟩
  · have he : x+(y+x)=y := by rw [add_comm y x,←add_assoc,vector_add_self,zero_add]
    rw [he]
    exact hy.1
  · have he : x+p.val+(y+x)=y+p.val := by
      calc _=(x+x)+(y+p.val) := by abel
           _=y+p.val := by rw [vector_add_self,zero_add]
    rw [he]
    exact hy.2

end Atlas.Rudvalis

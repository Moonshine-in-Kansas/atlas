import Atlas.Rudvalis.HeavyOrthogonalTranslations
import Atlas.Rudvalis.PointFixingTranslations

namespace Atlas.Rudvalis
local instance : DecidableEq E := Fintype.decidablePiFintype

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem quadratic_zero_pair_translation (b : E) (c p : Point) (hpc : p≠c)
    (hw : blockWeight 0 b c.val=2) (hp : dot b p.val+quadratic c.val p.val=0)
    (t : E) (ht : dot b t+quadratic c.val t=0)
    (hpt : dot b (p.val+t)+quadratic c.val (p.val+t)=0) :
    t=0 ∨ t=p.val ∨ t=c.val ∨ t=p.val+c.val := by
  decide +kernel +revert

theorem independent_point_functional (c p : Point) (hpc : p≠c) :
    ∃u : E,dot u c.val=0 ∧ dot u p.val=1 := by
  decide +kernel +revert

theorem fixedHeavyWord_row_quadratic (c : Point) (v : FixedHeavyParameters c) (p : Point) (y : E) :
    fixedHeavyWord c v (p,y)=v.2.val p+dot (matrixAt v.1.val p.val+eta p c.val) y+quadratic c.val y := by
  change v.2.val p+dot (matrixAt v.1.val p.val) y+theta p c.val y=_
  simp only [theta,dot_add_left]
  ring

theorem fixedHeavy_outer_stabilizes (c : Point) (v : FixedHeavyParameters c) (u : E)
    (hu : dot u c.val=0) :
    fixedHeavyWord c v ∘ coordinateTranslation (outerMatrix c.val u)=fixedHeavyWord c v := by
  rw [←fixedHeavyTranslate_word]
  change binaryNormalMap (translatedParameters (outerMatrix c.val u) (v.2.val,v.1.val,c.val))=_
  congr 1
  apply Prod.ext
  · funext p
    rw [translatedParameters_heavy_constant _ _ _ _ (LinearMap.mem_ker.mp v.1.prop),hu]
    simp
  · change (v.1.val+crossMatrix c.val*outerMatrix c.val u,c.val)=(v.1.val,c.val)
    rw [crossMatrix_outer_zero,add_zero]

theorem heavy_pair_translation_value (c p : Point) (hpc : p≠c)
    (v : HeavyAvoidingPair c p 0) (A : BinaryMatrix)
    (h0 : fixedHeavyWord c v.val (p,matrixAt A p.val)=0)
    (hp : fixedHeavyWord c v.val (p,p.val+matrixAt A p.val)=0) :
    matrixAt A p.val=0 ∨ matrixAt A p.val=p.val ∨
    matrixAt A p.val=c.val ∨ matrixAt A p.val=p.val+c.val := by
  have he : v.val.2.val p=0 := by
    have h := v.prop.1
    rw [fixedHeavyWord_row_quadratic] at h
    simpa [dot,quadratic] using h
  have hw := (binaryNormalMap_quadratic_weight_sixteen
    (v.val.2.val,v.val.1.val,c.val) c.prop).mp v.val.2.prop p
  have hne : p.val≠c.val := fun h => hpc (Subtype.ext h)
  simp only [hne,ite_false,he] at hw
  have hrow (y : E) : fixedHeavyWord c v.val (p,y)=
      dot (matrixAt v.val.1.val p.val+eta p c.val) y+quadratic c.val y := by
    rw [fixedHeavyWord_row_quadratic,he,zero_add]
  have hpp : dot (matrixAt v.val.1.val p.val+eta p c.val) p.val+quadratic c.val p.val=0 := by
    have hh := v.prop.2
    simpa only [zero_add,hrow] using hh
  rw [hrow] at h0 hp
  exact quadratic_zero_pair_translation _ c p hpc hw hpp _ h0 hp

/-- Correct any fixed-label translation by a rank-one support stabilizer. -/
theorem heavy_pair_fixing_translation (c p : Point) (hpc : p≠c)
    (v w : HeavyAvoidingPair c p 0) :
    ∃A : BinaryMatrix,FixesCoordinatePair p A ∧
      fixedHeavyWord c w.val=fixedHeavyWord c v.val ∘ coordinateTranslation A := by
  obtain ⟨A,hA⟩ := quadratic_minimum_fixed_radical_translation v.val.2.val w.val.2.val
    v.val.1.val w.val.1.val c.val c.prop v.val.2.prop w.val.2.prop
  change fixedHeavyWord c w.val=fixedHeavyWord c v.val ∘ coordinateTranslation A at hA
  have h0 : fixedHeavyWord c v.val (p,matrixAt A p.val)=0 := by
    have hh := congrFun hA (p,0)
    change fixedHeavyWord c w.val (p,0)=fixedHeavyWord c v.val (p,0+matrixAt A p.val) at hh
    simpa only [zero_add] using hh.symm.trans w.prop.1
  have hp : fixedHeavyWord c v.val (p,p.val+matrixAt A p.val)=0 := by
    have hh := congrFun hA (p,p.val)
    change fixedHeavyWord c w.val (p,p.val)=fixedHeavyWord c v.val (p,p.val+matrixAt A p.val) at hh
    exact hh.symm.trans (by simpa only [zero_add] using w.prop.2)
  rcases heavy_pair_translation_value c p hpc v A h0 hp with h|h|h|h
  · exact ⟨A,Or.inl h,hA⟩
  · exact ⟨A,Or.inr h,hA⟩
  all_goals
    obtain ⟨u,huc,hup⟩ := independent_point_functional c p hpc
    refine ⟨A+outerMatrix c.val u,?_,?_⟩
    · unfold FixesCoordinatePair
      rw [matrixAt_add,matrixAt_outer,hup,one_smul,h]
      simp only [add_assoc,vector_add_self,add_zero]
      simp
    · have hs := fixedHeavy_outer_stabilizes c v.val u huc
      funext z
      have hh := congrFun hA z
      have hs' := congrFun hs (coordinateTranslation A z)
      change fixedHeavyWord c w.val z=fixedHeavyWord c v.val (z.1,z.2+matrixAt (A+outerMatrix c.val u) z.1.val)
      rw [hh]
      change fixedHeavyWord c v.val (z.1,z.2+matrixAt A z.1.val)=_
      rw [matrixAt_add,←add_assoc]
      exact hs'.symm

end Atlas.Rudvalis

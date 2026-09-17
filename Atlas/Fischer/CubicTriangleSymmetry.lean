import Atlas.Fischer.CubicTriangleAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def cubicSextetSwapFirst : Equiv.Perm OrderedCubicSextetTriangle where
  toFun t := ⟨(t.val.2.1,t.val.1,t.val.2.2),by simpa only [add_comm] using t.property⟩
  invFun t := ⟨(t.val.2.1,t.val.1,t.val.2.2),by simpa only [add_comm] using t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def cubicTrioSwapFirst : Equiv.Perm OrderedCubicTrio where
  toFun t := ⟨(t.val.2.1,t.val.1,t.val.2.2),by rw [t.property,add_comm (octadWord t.val.1)]⟩
  invFun t := ⟨(t.val.2.1,t.val.1,t.val.2.2),by rw [t.property,add_comm (octadWord t.val.1)]⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cubicSextet_swapLast_relation (t : OrderedCubicSextetTriangle) :
    octadWord t.val.2.1=octadWord t.val.1+octadWord t.val.2.2 := by
  have h : octadWord t.val.2.2=octadWord t.val.2.1+octadWord t.val.1 := by
    simpa only [add_comm] using t.property
  simpa only [add_comm] using (octad_sum_switch _ _ _).mp h

theorem cubicTrio_swapLast_relation (t : OrderedCubicTrio) :
    octadWord t.val.2.1=octadWord t.val.1+octadWord t.val.2.2+golayOne := by
  have h : octadWord t.val.2.2=octadWord t.val.2.1+octadWord t.val.1+golayOne := by
    rw [t.property,add_comm (octadWord t.val.1)]
  have hh := (octad_complementary_sum_switch _ _ _).mp h
  simpa only [add_comm (octadWord t.val.2.2) (octadWord t.val.1)] using hh

def cubicSextetSwapLast : Equiv.Perm OrderedCubicSextetTriangle where
  toFun t := ⟨(t.val.1,t.val.2.2,t.val.2.1),cubicSextet_swapLast_relation t⟩
  invFun t := ⟨(t.val.1,t.val.2.2,t.val.2.1),cubicSextet_swapLast_relation t⟩
  left_inv _ := rfl
  right_inv _ := rfl

def cubicTrioSwapLast : Equiv.Perm OrderedCubicTrio where
  toFun t := ⟨(t.val.1,t.val.2.2,t.val.2.1),cubicTrio_swapLast_relation t⟩
  invFun t := ⟨(t.val.1,t.val.2.2,t.val.2.1),cubicTrio_swapLast_relation t⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cubicSextetIncidenceSum_swapFirst (i j k : Omega) :
    cubicSextetIncidenceSum i j k=cubicSextetIncidenceSum j i k := by
  unfold cubicSextetIncidenceSum
  rw [← Equiv.sum_comp cubicSextetSwapFirst]
  apply Finset.sum_congr rfl
  intro t ht
  change cubicPointOctadIncidence i t.val.2.1*cubicPointOctadIncidence j t.val.1*
    cubicPointOctadIncidence k t.val.2.2=_
  ring

theorem cubicSextetIncidenceSum_swapLast (i j k : Omega) :
    cubicSextetIncidenceSum i j k=cubicSextetIncidenceSum i k j := by
  unfold cubicSextetIncidenceSum
  rw [← Equiv.sum_comp cubicSextetSwapLast]
  apply Finset.sum_congr rfl
  intro t ht
  change cubicPointOctadIncidence i t.val.1*cubicPointOctadIncidence j t.val.2.2*
    cubicPointOctadIncidence k t.val.2.1=_
  ring

theorem cubicTrioIncidenceSum_swapFirst (i j k : Omega) :
    cubicTrioIncidenceSum i j k=cubicTrioIncidenceSum j i k := by
  unfold cubicTrioIncidenceSum
  rw [← Equiv.sum_comp cubicTrioSwapFirst]
  apply Finset.sum_congr rfl
  intro t ht
  change cubicPointOctadIncidence i t.val.2.1*cubicPointOctadIncidence j t.val.1*
    cubicPointOctadIncidence k t.val.2.2=_
  ring

theorem cubicTrioIncidenceSum_swapLast (i j k : Omega) :
    cubicTrioIncidenceSum i j k=cubicTrioIncidenceSum i k j := by
  unfold cubicTrioIncidenceSum
  rw [← Equiv.sum_comp cubicTrioSwapLast]
  apply Finset.sum_congr rfl
  intro t ht
  change cubicPointOctadIncidence i t.val.1*cubicPointOctadIncidence j t.val.2.2*
    cubicPointOctadIncidence k t.val.2.1=_
  ring

end Atlas.Fischer

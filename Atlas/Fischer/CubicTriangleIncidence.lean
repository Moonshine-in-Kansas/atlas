import Atlas.Fischer.CubicTriangleCounts
import Atlas.Fischer.OctadShortenedCode

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cubicTriangle_indicator_sum (S : Finset Omega) :
    (∑ i : Omega, if i ∈ S then (1 : Scalar) else 0)=(S.card : Scalar) := by
  rw [← Finset.sum_filter,Finset.sum_const]
  have h : Finset.univ.filter (fun i : Omega => i ∈ S)=S := by ext i; simp
  simp [h]

theorem cubicPointOctadIncidence_sum (D : Octad) :
    (∑ i : Omega,cubicPointOctadIncidence i D)=8 := by
  have h (i : Omega) : cubicPointOctadIncidence i D=
      4*(if i ∈ D.val then (1 : Scalar) else 0)-1 := by
    unfold cubicPointOctadIncidence
    split_ifs <;> norm_num
  simp_rw [h]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,cubicTriangle_indicator_sum,
    octad_size D.val D.property,Finset.sum_const,Finset.card_univ]
  have hc : Fintype.card Omega=24 := by decide
  rw [hc]
  norm_num

theorem cubicPointOctadIncidence_overlap_sum (D E : Octad) :
    (∑ i : Omega,cubicPointOctadIncidence i D*cubicPointOctadIncidence i E)=
      16*((D.val ∩ E.val).card : Scalar)-40 := by
  have h (i : Omega) : cubicPointOctadIncidence i D*cubicPointOctadIncidence i E=
      16*(if i ∈ D.val ∩ E.val then (1 : Scalar) else 0)-
      4*(if i ∈ D.val then 1 else 0)-4*(if i ∈ E.val then 1 else 0)+1 := by
    by_cases hD : i ∈ D.val <;> by_cases hE : i ∈ E.val <;>
      simp [cubicPointOctadIncidence,Finset.mem_inter,hD,hE] <;> norm_num
  simp_rw [h]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum,cubicTriangle_indicator_sum]
  rw [octad_size D.val D.property,octad_size E.val E.property,
    Finset.sum_const,Finset.card_univ]
  have hc : Fintype.card Omega=24 := by decide
  rw [hc]
  ring

theorem cubicSextetTriangle_intersection (t : OrderedCubicSextetTriangle) :
    (t.val.1.val ∩ t.val.2.1.val).card=4 :=
  (cubicSextetTrianglePairEquiv t).2.property

theorem cubicTrio_intersection (t : OrderedCubicTrio) :
    (t.val.1.val ∩ t.val.2.1.val).card=0 :=
  (cubicTrioPairEquiv t).2.property

theorem cubicSextetTriangle_pair_sum (t : OrderedCubicSextetTriangle) :
    (∑ i : Omega,cubicPointOctadIncidence i t.val.1*
      cubicPointOctadIncidence i t.val.2.1)=24 := by
  rw [cubicPointOctadIncidence_overlap_sum,cubicSextetTriangle_intersection t]
  norm_num

theorem cubicTrio_pair_sum (t : OrderedCubicTrio) :
    (∑ i : Omega,cubicPointOctadIncidence i t.val.1*
      cubicPointOctadIncidence i t.val.2.1)= -40 := by
  rw [cubicPointOctadIncidence_overlap_sum,cubicTrio_intersection t]
  norm_num

theorem cubicSextetTriangle_pointwise (t : OrderedCubicSextetTriangle) (i : Omega) :
    cubicPointOctadIncidence i t.val.1*cubicPointOctadIncidence i t.val.2.1*
      cubicPointOctadIncidence i t.val.2.2=
      -1-8*(if i ∈ t.val.1.val ∪ t.val.2.1.val then (1 : Scalar) else 0) := by
  have h := congrArg (fun c : golay => c.val i) t.property
  simp only [Submodule.coe_add,Pi.add_apply,octadWord_apply] at h
  by_cases hD : i ∈ t.val.1.val <;> by_cases hE : i ∈ t.val.2.1.val <;>
    by_cases hF : i ∈ t.val.2.2.val <;>
    simp [cubicPointOctadIncidence,hD,hE,hF,show (2 : Bit)=0 from rfl] at h ⊢ <;> norm_num

theorem cubicSextetTriangle_triple_sum (t : OrderedCubicSextetTriangle) :
    (∑ i : Omega,cubicPointOctadIncidence i t.val.1*
      cubicPointOctadIncidence i t.val.2.1*cubicPointOctadIncidence i t.val.2.2)= -120 := by
  simp_rw [cubicSextetTriangle_pointwise]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,cubicTriangle_indicator_sum,
    Finset.sum_const,Finset.card_univ]
  have hu : (t.val.1.val ∪ t.val.2.1.val).card=12 := by
    have h := Finset.card_union_add_card_inter t.val.1.val t.val.2.1.val
    rw [octad_size _ t.val.1.property,octad_size _ t.val.2.1.property,
      cubicSextetTriangle_intersection t] at h
    omega
  have hc : Fintype.card Omega=24 := by decide
  rw [hu,hc]
  norm_num

theorem cubicTrio_pointwise (t : OrderedCubicTrio) (i : Omega) :
    cubicPointOctadIncidence i t.val.1*cubicPointOctadIncidence i t.val.2.1*
      cubicPointOctadIncidence i t.val.2.2=3 := by
  have h := congrArg (fun c : golay => c.val i) t.property
  simp only [Submodule.coe_add,Pi.add_apply,octadWord_apply,golayOne,allOnes] at h
  have hn : ¬(i ∈ t.val.1.val ∧ i ∈ t.val.2.1.val) := by
    intro hi
    have hp : 0 < (t.val.1.val ∩ t.val.2.1.val).card :=
      Finset.card_pos.mpr ⟨i,Finset.mem_inter.mpr hi⟩
    rw [cubicTrio_intersection t] at hp
    omega
  by_cases hD : i ∈ t.val.1.val <;> by_cases hE : i ∈ t.val.2.1.val <;>
    by_cases hF : i ∈ t.val.2.2.val <;>
    simp [cubicPointOctadIncidence,hD,hE,hF,show (2 : Bit)=0 from rfl] at h hn ⊢ <;> norm_num

theorem cubicTrio_triple_sum (t : OrderedCubicTrio) :
    (∑ i : Omega,cubicPointOctadIncidence i t.val.1*
      cubicPointOctadIncidence i t.val.2.1*cubicPointOctadIncidence i t.val.2.2)=72 := by
  simp_rw [cubicTrio_pointwise]
  rw [Finset.sum_const,Finset.card_univ]
  have hc : Fintype.card Omega=24 := by decide
  rw [hc]
  norm_num

end Atlas.Fischer

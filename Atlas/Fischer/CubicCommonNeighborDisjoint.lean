import Atlas.Fischer.CubicTriangleModels
import Atlas.Fischer.OctadHyperplanePairs

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable
local instance cubicCommonNeighborHyperplaneFintype (D : Octad) :
    Fintype (OctadShortenedHyperplane D) := Fintype.ofFinite _

def cubicDisjointHyperplaneOctad (D : Octad) (b : OctadShortenedHyperplane D) :
    CubicOctadIntersectionRow D 0 :=
  ⟨⟨support b.val.val.val,(octads_mem _).mpr
      ⟨b.val.val,octadShortenedHyperplane_weight D b,rfl⟩⟩,by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hz := (mem_octadShortenedCode D b.val.val).mp b.val.property i (Finset.mem_inter.mp hi).1
    have hn := (Finset.mem_inter.mp hi).2
    simpa only [support,Finset.mem_filter,Finset.mem_univ,true_and,hz,ne_eq,not_true_eq_false] using hn⟩

theorem cubicDisjointHyperplaneOctad_injective (D : Octad) :
    Function.Injective (cubicDisjointHyperplaneOctad D) := by
  intro b c h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply support_injective
  exact congrArg (fun G : CubicOctadIntersectionRow D 0 => G.val.val) h

def cubicDisjointHyperplaneEquiv (D : Octad) :
    OctadShortenedHyperplane D ≃ CubicOctadIntersectionRow D 0 :=
  Equiv.ofBijective (cubicDisjointHyperplaneOctad D) (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨cubicDisjointHyperplaneOctad_injective D,?_⟩
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,
      octadShortenedHyperplane_natCard,cubicOctadIntersectionRow_card,
      (octad_intersection_distribution D.val D.property).1])

theorem cubicDisjointHyperplane_intersection_iff (D : Octad)
    (b c : OctadShortenedHyperplane D) :
    ((cubicDisjointHyperplaneEquiv D b).val.val ∩
      (cubicDisjointHyperplaneEquiv D c).val.val).card=4 ↔
      b.val+c.val ≠ 0 ∧ b.val+c.val ≠ octadShortenedOne D := by
  change (support b.val.val.val ∩ support c.val.val.val).card=4 ↔ _
  rw [← overlap_inter]
  have hw := binary_weight_add b.val.val.val c.val.val.val
  rw [octadShortenedHyperplane_weight D b,octadShortenedHyperplane_weight D c] at hw
  constructor
  · intro h4
    have hs : hammingNorm (b.val+c.val).val.val=8 := by
      change hammingNorm (b.val.val.val+c.val.val.val)=8
      omega
    constructor
    · intro hz
      rw [hz] at hs
      norm_num at hs
    · intro hz
      rw [hz] at hs
      change hammingNorm (octadComplementWord D).val=8 at hs
      rw [octadComplementWord_weight] at hs
      omega
  · intro h
    have hs := octadShortenedHyperplane_weight D ⟨b.val+c.val,h⟩
    change hammingNorm (b.val.val.val+c.val.val.val)=8 at hs
    omega

/-- For a fixed disjoint pair, the other exterior hyperplanes meeting the
second octad in four points are exactly the 28 nonconstant affine sums. -/
theorem cubicCommonNeighbor_disjoint_pair_twentyEight (D F : Octad)
    (hDF : (D.val ∩ F.val).card=0) :
    Nat.card {G : Octad // (D.val ∩ G.val).card=0 ∧ (F.val ∩ G.val).card=4}=28 := by
  let c := (cubicDisjointHyperplaneEquiv D).symm ⟨F,hDF⟩
  let e : {b : OctadShortenedHyperplane D // b.val+c.val ≠ 0 ∧ b.val+c.val ≠ octadShortenedOne D} ≃
      {G : Octad // (D.val ∩ G.val).card=0 ∧ (F.val ∩ G.val).card=4} :=
    { toFun := fun b => ⟨(cubicDisjointHyperplaneEquiv D b.val).val,⟨
        (cubicDisjointHyperplaneEquiv D b.val).property,by
          have hh := (cubicDisjointHyperplane_intersection_iff D b.val c).mpr b.property
          have hc : (cubicDisjointHyperplaneEquiv D c).val=F := by simp [c]
          rw [hc,Finset.inter_comm] at hh
          exact hh⟩⟩
      invFun := fun G => ⟨(cubicDisjointHyperplaneEquiv D).symm ⟨G.val,G.property.1⟩,by
        apply (cubicDisjointHyperplane_intersection_iff D _ c).mp
        simp only [Equiv.apply_symm_apply]
        have hc : (cubicDisjointHyperplaneEquiv D c).val=F := by simp [c]
        rw [hc,Finset.inter_comm]
        exact G.property.2⟩
      left_inv := by intro b; apply Subtype.ext; exact Equiv.symm_apply_apply _ b.val
      right_inv := by intro G; apply Subtype.ext; exact congrArg (fun z : CubicOctadIntersectionRow D 0 => z.val) (Equiv.apply_symm_apply (cubicDisjointHyperplaneEquiv D) (⟨G.val,G.property.1⟩ : CubicOctadIntersectionRow D 0)) }
  rw [← Nat.card_congr e,Nat.card_eq_fintype_card,octadShortenedHyperplane_sum_card]

end Atlas.Fischer

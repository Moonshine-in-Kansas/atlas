import Atlas.Fischer.ResidueQuotientGeneration
import Atlas.Fischer.ResidueKernelCocode
import Atlas.Fischer.ResidueElementaryCocode

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual cocode action lifts into each marked centralizer. -/
def residueCocodeCentralizer (S : Finset Omega) : Multiplicative Cocode →* residueCentralizer S :=
  generatedCocodeRayHom.codRestrict _ (by
    intro d
    have hd : generatedCocodeRayHom d ∈ basicFramePointwiseRayStabilizer := by
      rw [basicFramePointwiseRayStabilizer_eq_cocode]
      exact ⟨d,rfl⟩
    rintro x ⟨i,hi,rfl⟩
    exact hd _ ⟨i,rfl⟩)

def residueCocodeQuotient (S : Finset Omega) : Multiplicative Cocode →* ResidueGroup S :=
  (QuotientGroup.mk' (residueCentralElementary S)).comp (residueCocodeCentralizer S)

theorem residueCocodeQuotient_basic (S : Finset Omega) (i : Omega) (hi : i ∉ S) :
    residueCocodeQuotient S (cocodeInvolution i)=
      residueDistinguishedElement S (residueBasicPoint S i hi) := by
  apply congrArg (QuotientGroup.mk' (residueCentralElementary S))
  apply Subtype.ext
  exact generatedCocodeRayHom_coordinate i

theorem residueCocodeQuotient_marked (S : Finset Omega) (i : Omega) (hi : i ∈ S) :
    residueCocodeQuotient S (cocodeInvolution i)=1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  change generatedCocodeRayHom (cocodeInvolution i) ∈ residueElementary S
  change generatedCocodeRayHom (Multiplicative.ofAdd (coordinateCocode i)) ∈ residueElementary S
  rw [generatedCocodeRayHom_coordinate]
  exact Subgroup.subset_closure ⟨i,hi,rfl⟩

/-- The seven original basic residue points left by an octad meeting the marks once. -/
def residueOctadList (S : Finset Omega) (O : Octad) : List (ResiduePoint S) :=
  (O.val \ S).attach.toList.map (fun i => residueBasicPoint S i.val (Finset.mem_sdiff.mp i.prop).2)

theorem residueOctadList_length (S : Finset Omega) (O : Octad)
    (h : (O.val ∩ S).card=1) : (residueOctadList S O).length=7 := by
  classical
  simp only [residueOctadList,List.length_map,Finset.length_toList,Finset.card_attach]
  have hc := Finset.card_sdiff_add_card_inter O.val S
  have hO : O.val.card=8 := octad_size O.val O.prop
  omega

/-- The remaining seven actual involutions have product one in the central quotient. -/
theorem residueOctadList_relation (S : Finset Omega) (O : Octad) :
    ((residueOctadList S O).map (residueDistinguishedElement S)).prod=1 := by
  classical
  let f := residueCocodeQuotient S
  have hO : (∏ i ∈ O.val,cocodeInvolution i)=1 :=
    (cocodeInvolutions_relation O.val).mpr (by
      have hw := binarySupportEquiv.symm_apply_apply (octadWord O).val
      change binarySupportEquiv.symm (support (octadWord O).val)=(octadWord O).val at hw
      rw [octadWord_support] at hw
      rw [hw]
      exact (octadWord O).prop)
  have hm (T : Finset Omega) (hT : T ⊆ S) : f (∏ i ∈ T,cocodeInvolution i)=1 := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert i T hi ih =>
      rw [Finset.prod_insert hi,map_mul,residueCocodeQuotient_marked S i (hT (Finset.mem_insert_self _ _)),
        ih (fun j hj => hT (Finset.mem_insert_of_mem hj)),one_mul]
  have hI : f (∏ i ∈ O.val ∩ S,cocodeInvolution i)=1 := hm _ Finset.inter_subset_right
  have hs : f (∏ i ∈ O.val \ S,cocodeInvolution i)=1 := by
    have hp := Finset.prod_sdiff (f := cocodeInvolution) (Finset.inter_subset_left : O.val ∩ S ⊆ O.val)
    have he : O.val \ (O.val ∩ S)=O.val \ S := by ext i; simp
    rw [he] at hp
    have h := congrArg f hp
    rw [map_mul,hI,mul_one,hO,map_one] at h
    exact h
  rw [residueOctadList,List.map_map]
  have he : (fun i : {i // i ∈ O.val \ S} =>
      residueDistinguishedElement S (residueBasicPoint S i.val (Finset.mem_sdiff.mp i.prop).2)) =
      fun i => f (cocodeInvolution i.val) := by
    funext i
    exact (residueCocodeQuotient_basic S i.val _).symm
  dsimp only [Function.comp_def]
  rw [he]
  change ((O.val \ S).attach.toList.map ((⇑f) ∘ (fun i => cocodeInvolution i.val))).prod=1
  rw [← List.map_map,← map_list_prod]
  simpa only [Finset.prod_map_toList,Finset.prod_attach] using hs

end Atlas.Fischer

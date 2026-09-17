import Atlas.Conway.EisensteinTriadUnitFrames

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem eisensteinOneModThree_frame_syndrome (x y : EisensteinShell 6)
    (a b : EisensteinCoordinates) (ha : ∀ i, x.val.val i=1+3*a i)
    (hb : ∀ i, y.val.val i=1+3*b i) (t s : ternaryGolay)
    (h : eisensteinFrameOfVector (eisensteinCodePhaseShell t x)=
      eisensteinFrameOfVector (eisensteinCodePhaseShell s y)) :
    ternarySyndromeClass (eisensteinWordResidue a)=ternarySyndromeClass (eisensteinWordResidue b) := by
  have he := ((eisensteinOneModThree_frame_phase_iff x y ⟨a,ha⟩ ⟨b,hb⟩ t s).mp h).1
  have hc : eisensteinClass x.val=eisensteinClass y.val :=
    ((eisensteinFramePair_eq_iff _ _).mp (congrArg Subtype.val he)).resolve_right
      (eisensteinClass_not_neg_of_residue_one _ _
        (eisensteinOneModThree_residue _ ⟨a,ha⟩ 0)
        (eisensteinOneModThree_residue _ ⟨b,hb⟩ 0))
  have hm := ((eisensteinOneModThree_class_iff x.val y.val a b ha hb).mp hc).1
  apply (ternarySyndromeClass_eq_iff _ _).mpr
  convert hm using 1
  ext i
  exact (map_sub eisensteinResidue _ _).symm

end Atlas.Conway

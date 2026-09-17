import Atlas.GroupTheory.CommutingFrameTransport
import Atlas.Fischer.CommutingFrameConjugacy

noncomputable section
namespace Atlas.Fischer

abbrev FischerFrame := {F : Set rootGeneratedRayGroup // IsFischerFrame F}

theorem distinguishedRootClass_conjugation (g : rootGeneratedRayGroup) :
    (MulAut.conj g) '' Set.range distinguishedRootElement = Set.range distinguishedRootElement := by
  have hf (g : rootGeneratedRayGroup) (x : rootGeneratedRayGroup)
      (hx : x ∈ Set.range distinguishedRootElement) :
      MulAut.conj g x ∈ Set.range distinguishedRootElement := by
    obtain ⟨i,rfl⟩ := hx
    obtain ⟨j,hj⟩ := displayedRayOfParameter_surjective (g.val (displayedRayOfParameter i))
    exact ⟨j,(distinguishedRootElement_conjugation g i j hj.symm).symm⟩
  apply Set.Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩; exact hf g y hy
  · intro x hx
    refine ⟨MulAut.conj g⁻¹ x,hf g⁻¹ x hx,?_⟩
    simp [MulAut.conj_apply,mul_assoc]

def fischerFrameConjugate (g : rootGeneratedRayGroup) (F : FischerFrame) : FischerFrame :=
  ⟨(MulAut.conj g) '' F.val,F.property.image _ (distinguishedRootClass_conjugation g)⟩

instance fischerFrameMulAction : MulAction rootGeneratedRayGroup FischerFrame where
  smul := fischerFrameConjugate
  one_smul F := by
    apply Subtype.ext
    change (MulAut.conj (1 : rootGeneratedRayGroup)) '' F.val = F.val
    simp [MulAut.conj_apply]
  mul_smul g h F := by
    apply Subtype.ext
    change (MulAut.conj (g*h)) '' F.val = (MulAut.conj g) '' ((MulAut.conj h) '' F.val)
    rw [Set.image_image]
    congr 1

@[simp] theorem fischerFrame_smul_val (g : rootGeneratedRayGroup) (F : FischerFrame) :
    (g • F).val = (MulAut.conj g) '' F.val := rfl

theorem fischerFrame_transitive : MulAction.IsPretransitive rootGeneratedRayGroup FischerFrame := by
  constructor
  intro F K
  obtain ⟨g,hg⟩ := fischerFrames_conjugate F.val K.val F.property K.property
  exact ⟨g,Subtype.ext hg⟩

end Atlas.Fischer

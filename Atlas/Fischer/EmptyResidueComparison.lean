import Atlas.Fischer.ResidueQuotientGeometry
import Mathlib.GroupTheory.GroupAction.Primitive

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem residueCentralizer_empty : residueCentralizer ∅=⊤ := by
  simp [residueCentralizer,markedPentadPointwise]

def rootGeneratedEmptyCentralizerHom : rootGeneratedRayGroup →* residueCentralizer ∅ where
  toFun g := ⟨g,by rw [residueCentralizer_empty]; trivial⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def rootGeneratedEmptyResidueHom : rootGeneratedRayGroup →* ResidueGroup ∅ :=
  (QuotientGroup.mk' (residueCentralElementary ∅)).comp rootGeneratedEmptyCentralizerHom

theorem rootGeneratedEmptyResidueHom_surjective :
    Function.Surjective rootGeneratedEmptyResidueHom := by
  intro y
  obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨x.val,rfl⟩

theorem rootGeneratedEmptyResidueHom_injective :
    Function.Injective rootGeneratedEmptyResidueHom := by
  apply (injective_iff_map_eq_one rootGeneratedEmptyResidueHom).mpr
  intro g hg
  have he := (QuotientGroup.eq_one_iff (rootGeneratedEmptyCentralizerHom g)).mp hg
  change g ∈ Subgroup.closure (residueBasicSet ∅) at he
  simpa [residueBasicSet] using he

/-- The empty central quotient is the same constructed largest ray group. -/
def rootGeneratedEmptyResidueEquiv : rootGeneratedRayGroup ≃* ResidueGroup ∅ :=
  MulEquiv.ofBijective rootGeneratedEmptyResidueHom
    ⟨rootGeneratedEmptyResidueHom_injective,rootGeneratedEmptyResidueHom_surjective⟩

def displayedRayEmptyResidueEquiv : DisplayedReflectingRay ≃ ResiduePoint ∅ :=
  displayedRayDistinguishedEquiv.trans
    { toFun := fun x => ⟨x.val,x.property,by simp [residueBasicSet],by simp⟩
      invFun := fun x => ⟨x.val,x.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def displayedRayEmptyResidueMap :
    DisplayedReflectingRay →ₑ[rootGeneratedEmptyResidueHom] ResiduePoint ∅ where
  toFun := displayedRayEmptyResidueEquiv
  map_smul' g x := by
    apply Subtype.ext
    exact displayedRayDistinguishedEquiv_equivariant g x

/-- Transfer the proved empty-residue action back to the original ray action. -/
theorem rootGeneratedRay_primitive_of_empty_residue
    (h : MulAction.IsPreprimitive (ResidueGroup ∅) (ResiduePoint ∅)) :
    MulAction.IsPreprimitive rootGeneratedRayGroup DisplayedReflectingRay :=
  (MulAction.isPreprimitive_congr (f := displayedRayEmptyResidueMap)
    rootGeneratedEmptyResidueHom_surjective displayedRayEmptyResidueEquiv.bijective).mpr h

end Atlas.Fischer

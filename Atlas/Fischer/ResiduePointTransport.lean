import Atlas.Fischer.ResidueTransport
import Atlas.Fischer.ResidueAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

private theorem residuePoint_condition_transport (S T : Finset Omega)
    (e : MulAut rootGeneratedRayGroup)
    (hD : e '' Set.range distinguishedRootElement = Set.range distinguishedRootElement)
    (h : e '' residueBasicSet S = residueBasicSet T) (x : ResiduePoint S) :
    e x.val ∈ Set.range distinguishedRootElement ∧ e x.val ∉ residueBasicSet T ∧
      ∀ i ∈ T, Commute (distinguishedRootElement (.inl i)) (e x.val) := by
  refine ⟨?_,?_,?_⟩
  · exact (Set.ext_iff.mp hD _).mp ⟨x.val,x.property.1,rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨z,hz,hzx⟩ := hx
    exact x.property.2.1 ((e.injective hzx) ▸ hz)
  · intro i hi
    have hm : distinguishedRootElement (.inl i) ∈ e '' residueBasicSet S := by
      rw [h]
      exact ⟨i,hi,rfl⟩
    obtain ⟨z,⟨j,hj,rfl⟩,hz⟩ := hm
    rw [← hz]
    exact (x.property.2.2 j hj).map e

/-- The same conjugation transports the original residue points, before quotient images. -/
def residuePointTransport (S T : Finset Omega) (g : rootGeneratedRayGroup)
    (h : (MulAut.conj g) '' residueBasicSet S = residueBasicSet T) :
    ResiduePoint S ≃ ResiduePoint T := by
  have hi : (MulAut.conj g).symm '' residueBasicSet T = residueBasicSet S := by
    rw [← h,Set.image_image]
    simp only [MulEquiv.symm_apply_apply]
    simp
  have hD : (MulAut.conj g).symm '' Set.range distinguishedRootElement =
      Set.range distinguishedRootElement := by
    calc
      _ = (MulAut.conj g).symm '' ((MulAut.conj g) '' Set.range distinguishedRootElement) :=
        congrArg (fun A => (MulAut.conj g).symm '' A) (distinguishedRootClass_conjugation g).symm
      _ = _ := by
        rw [Set.image_image]
        simp only [MulEquiv.symm_apply_apply]
        simp
  exact {
    toFun := fun x => ⟨MulAut.conj g x.val,
      residuePoint_condition_transport S T _ (distinguishedRootClass_conjugation g) h x⟩
    invFun := fun x => ⟨(MulAut.conj g).symm x.val,
      residuePoint_condition_transport T S _ hD hi x⟩
    left_inv := fun x => Subtype.ext ((MulAut.conj g).symm_apply_apply x.val)
    right_inv := fun x => Subtype.ext ((MulAut.conj g).apply_symm_apply x.val) }

@[simp] theorem residuePointTransport_val (S T : Finset Omega) (g : rootGeneratedRayGroup)
    (h : (MulAut.conj g) '' residueBasicSet S = residueBasicSet T) (x : ResiduePoint S) :
    (residuePointTransport S T g h x).val = g*x.val*g⁻¹ := rfl

theorem residuePointTransport_equivariant (S T : Finset Omega) (g : rootGeneratedRayGroup)
    (h : (MulAut.conj g) '' residueBasicSet S = residueBasicSet T)
    (a : residueCentralizer S) (x : ResiduePoint S) :
    residuePointTransport S T g h (a • x) =
      residueCentralizerTransport S T g h a • residuePointTransport S T g h x := by
  apply Subtype.ext
  simp only [residuePointTransport_val,residuePoint_smul_val,residueCentralizerTransport_val]
  group

end Atlas.Fischer

import Atlas.Fischer.FischerFrameAction
import Atlas.Fischer.MarkedPentadFrames
import Atlas.Fischer.OrderedCommutingTupleAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual pointwise centralizer of the marked basic involutions. -/
def markedPentadPointwise (S : Finset Omega) : Subgroup rootGeneratedRayGroup :=
  Subgroup.centralizer ((fun i : Omega => distinguishedRootElement (.inl i)) '' (S : Set Omega))

theorem mem_markedPentadPointwise_iff (S : Finset Omega) (g : rootGeneratedRayGroup) :
    g ∈ markedPentadPointwise S ↔ ∀ i ∈ S,
      g * distinguishedRootElement (.inl i) * g⁻¹ = distinguishedRootElement (.inl i) := by
  rw [markedPentadPointwise,Subgroup.mem_centralizer_iff]
  constructor
  · intro h i hi
    have hc := h _ ⟨i,hi,rfl⟩
    calc
      g * distinguishedRootElement (.inl i) * g⁻¹ =
        distinguishedRootElement (.inl i) * g * g⁻¹ := by rw [hc]
      _ = _ := by group
  · intro h x hx
    obtain ⟨i,hi,rfl⟩ := hx
    have hh := congrArg (fun x => x*g) (h i hi)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh.symm

def markedPentadFrameConjugate (S : Finset Omega) (g : markedPentadPointwise S)
    (F : MarkedPentadFrame S) : MarkedPentadFrame S := by
  refine ⟨(MulAut.conj g.val) '' F.val,
    F.property.1.image _ (distinguishedRootClass_conjugation g.val),?_⟩
  intro i hi
  exact ⟨distinguishedRootElement (.inl i),F.property.2 i hi,
    (mem_markedPentadPointwise_iff S g.val).mp g.property i hi⟩

instance markedPentadFrameMulAction (S : Finset Omega) :
    MulAction (markedPentadPointwise S) (MarkedPentadFrame S) where
  smul := markedPentadFrameConjugate S
  one_smul F := by
    apply Subtype.ext
    change (MulAut.conj (1 : rootGeneratedRayGroup)) '' F.val = F.val
    simp [MulAut.conj_apply]
  mul_smul g h F := by
    apply Subtype.ext
    change (MulAut.conj (g.val*h.val)) '' F.val =
      (MulAut.conj g.val) '' ((MulAut.conj h.val) '' F.val)
    rw [Set.image_image]
    congr 1

@[simp] theorem markedPentadFrame_smul_val (S : Finset Omega)
    (g : markedPentadPointwise S) (F : MarkedPentadFrame S) :
    (g • F).val = (MulAut.conj g.val) '' F.val := rfl

end Atlas.Fischer

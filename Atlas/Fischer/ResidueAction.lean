import Atlas.Fischer.ResidueModels

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Conjugation on the original distinguished elements of the residue. -/
def residueConjugate (S : Finset Omega) (g : residueCentralizer S) (x : ResiduePoint S) :
    ResiduePoint S := by
  refine ⟨MulAut.conj g.val x.val,?_,?_,?_⟩
  · exact (Set.ext_iff.mp (distinguishedRootClass_conjugation g.val) _).mp
      ⟨x.val,x.property.1,rfl⟩
  · rintro ⟨i,hi,he⟩
    have hg := (mem_markedPentadPointwise_iff S g.val).mp g.property i hi
    apply x.property.2.1
    refine ⟨i,hi,?_⟩
    apply (MulAut.conj g.val).injective
    exact hg.trans he
  · intro i hi
    have hc := (x.property.2.2 i hi).map (MulAut.conj g.val)
    have hg := (mem_markedPentadPointwise_iff S g.val).mp g.property i hi
    change Commute (g.val * distinguishedRootElement (.inl i) * g.val⁻¹) _ at hc
    rw [hg] at hc
    exact hc

instance residuePointMulAction (S : Finset Omega) : MulAction (residueCentralizer S) (ResiduePoint S) where
  smul := residueConjugate S
  one_smul x := by
    apply Subtype.ext
    change (1 : rootGeneratedRayGroup)*x.val*1⁻¹=x.val
    simp
  mul_smul g h x := by
    apply Subtype.ext
    change (g.val*h.val)*x.val*(g.val*h.val)⁻¹ =
      g.val*(h.val*x.val*h.val⁻¹)*g.val⁻¹
    group

@[simp] theorem residuePoint_smul_val (S : Finset Omega) (g : residueCentralizer S) (x : ResiduePoint S) :
    (g • x).val = g.val*x.val*g.val⁻¹ := rfl

def residueConjugationHom (S : Finset Omega) : residueCentralizer S →* Equiv.Perm (ResiduePoint S) :=
  MulAction.toPermHom _ _

theorem mem_residueAction_kernel_iff (S : Finset Omega) (g : residueCentralizer S) :
    g ∈ (residueConjugationHom S).ker ↔ ∀ x : ResiduePoint S, g.val*x.val*g.val⁻¹=x.val := by
  change (MulAction.toPermHom _ _) g=1 ↔ _
  rw [Equiv.ext_iff]
  constructor
  · intro h x; exact congrArg Subtype.val (h x)
  · intro h x; exact Subtype.ext (h x)

theorem residueElementary_le_action_kernel (S : Finset Omega) :
    residueCentralElementary S ≤ (residueConjugationHom S).ker := by
  intro g hg
  apply (mem_residueAction_kernel_iff S g).mpr
  intro x
  have hcent : residueElementary S ≤ Subgroup.centralizer ({x.val} : Set rootGeneratedRayGroup) := by
    apply (Subgroup.closure_le _).mpr
    rintro y ⟨i,hi,rfl⟩
    rintro z rfl
    exact (x.property.2.2 i hi).eq.symm
  have hc := hcent hg x.val (Set.mem_singleton _)
  change x.val*g.val=g.val*x.val at hc
  rw [← hc]
  group

end Atlas.Fischer

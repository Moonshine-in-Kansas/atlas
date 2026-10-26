import Atlas.Codes.QuaternaryMonomial
import Atlas.Rudvalis.SignKernel
import Atlas.Rudvalis.BinaryTranslations

/-! The full signed coordinate stabilizer of the actual quaternary code. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

/-- Full signed code group, before its projection is proved surjective. -/
def codeGroup : Subgroup (SignedCoordinates Coordinate) where
  carrier := {g | ∀ w, w∈quaternaryCode ↔ monomialHom g w∈quaternaryCode}
  one_mem' := by intro w; simp
  mul_mem' := by
    intro g h hg hh w
    rw [map_mul]
    exact (hh w).trans (hg (monomialHom h w))
  inv_mem' := by
    intro g hg w
    have h := hg (monomialHom g⁻¹ w)
    simpa using h.symm

theorem codeGroup_residue_preserves (g : codeGroup) (d : BinaryWord) (hd : d∈binaryResidue) :
    d ∘ g.val.right.symm∈binaryResidue := by
  obtain ⟨w,hw,rfl⟩ := (quaternaryCode_residue d).mp hd
  rw [← monomialAction_reduce]
  exact (quaternaryCode_residue _).mpr ⟨monomialHom g.val w,(g.prop w).mp hw,rfl⟩

theorem codeGroup_permutation_mem (g : codeGroup) : g.val.right∈binaryPermutationGroup := by
  intro d
  constructor
  · intro hd
    exact codeGroup_residue_preserves g⁻¹ d hd
  · intro hd
    have h := codeGroup_residue_preserves g (d ∘ g.val.right) hd
    simpa [Function.comp_def] using h

def codePermutationHom : codeGroup →* binaryPermutationGroup where
  toFun g := ⟨g.val.right,codeGroup_permutation_mem g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem codePermutationHom_kernel (g : codeGroup) :
    g∈codePermutationHom.ker ↔ g.val.right=1 := by
  change (⟨g.val.right,codeGroup_permutation_mem g⟩ : binaryPermutationGroup)=1 ↔ _
  exact Subtype.ext_iff

theorem codeGroup_sign_mem (s : BinaryWord) :
    (SemidirectProduct.inl (Multiplicative.ofAdd s) : SignedCoordinates Coordinate)∈codeGroup ↔
      s∈signPatterns := by
  rw [signPatterns_iff_preserves]
  constructor
  · intro h w hw
    exact (h w).mp hw
  · intro h w
    constructor
    · exact h w
    · intro hw
      have hh := h (signChange s w) hw
      have he : signChange s (signChange s w)=w := (signChange s).left_inv w
      rwa [he] at hh

end Atlas.Rudvalis

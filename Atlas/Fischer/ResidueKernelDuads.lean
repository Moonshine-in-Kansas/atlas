import Atlas.Fischer.ResidueKernelCocode
import Atlas.Fischer.ResidueElementaryCocode
import Atlas.Fischer.DuadicCocodeRayStabilizer

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def residueDuadicPoint (S : Finset Omega) (p : RootDuad) (hSp : S ⊆ p.val)
    (ξ : Module.Dual Bit (duadShortenedCode p.val)) : ResiduePoint S := by
  let t : ReflectingRootParameter := .inr (.inr ⟨p,ξ⟩)
  refine ⟨distinguishedRootElement t,⟨t,rfl⟩,?_,?_⟩
  · rintro ⟨i,hi,he⟩
    have hh := distinguishedRootElement_injective he
    change Sum.inl i = (Sum.inr (Sum.inr ⟨p,ξ⟩) : ReflectingRootParameter) at hh
    cases hh
  · intro i hi
    apply (distinguishedRoot_commute_iff _ _).mpr
    change hermitian (basicAxis i) (chosenDuadicRoot p ξ) ≠ 0
    rw [hermitian_basicAxis_duadic,if_pos (hSp hi)]
    exact one_ne_zero

/-- A kernel cocode lies in every actual duadic coordinate span containing S. -/
theorem residueAction_kernel_duad_span (S : Finset Omega) (g : residueCentralizer S)
    (hg : g ∈ (residueConjugationHom S).ker) (d : Multiplicative Cocode)
    (hd : g.val = generatedCocodeRayHom d) (p : RootDuad) (hSp : S ⊆ p.val) :
    d.toAdd ∈ coordinateCocodeSpan p.val := by
  apply (generatedCocodeRayHom_duadic_stabilizer p d 0).mp
  rw [← hd]
  apply displayedRayDistinguishedEquiv.injective
  apply Subtype.ext
  rw [displayedRayDistinguishedEquiv_equivariant,displayedRayDistinguishedEquiv_parameter]
  exact (mem_residueAction_kernel_iff S g).mp hg (residueDuadicPoint S p hSp 0)

end Atlas.Fischer

import Atlas.Rudvalis.CodeGroup
import Atlas.Rudvalis.BinaryPermutationTorsion
import Atlas.Rudvalis.SeedResidueSpanning
import Atlas.Rudvalis.BinaryLiftAction

/-! Signed seed preservation implies preservation of both binary layers and the code. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

def binaryPullback (p : Equiv.Perm Coordinate) : BinaryWord →ₗ[Bit] BinaryWord where
  toFun d := d ∘ p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem monomial_seed_residue (g : SignedCoordinates Coordinate)
    (hs : ∀ t, monomialHom g (quaternarySeed t)∈quaternaryCode) :
    ∀ d, d∈binaryResidue → d ∘ g.right.symm∈binaryResidue := by
  have hle : binaryResidue≤binaryResidue.comap (binaryPullback g.right.symm) := by
    nth_rw 1 [← seedOrbitResidue_span]
    apply Submodule.span_le.mpr
    rintro d ⟨t,rfl⟩
    change seedOrbitResidue t ∘ g.right.symm∈binaryResidue
    have hr : reduce (quaternarySeed t)=seedOrbitResidue t := quaternarySeed_reduce t
    rw [← hr,← monomialAction_reduce]
    exact (quaternaryCode_residue _).mpr ⟨_,hs t,rfl⟩
  exact fun _ hd => hle hd

theorem monomial_seed_permutation (g : SignedCoordinates Coordinate)
    (hs : ∀ t, monomialHom g (quaternarySeed t)∈quaternaryCode)
    (hi : ∀ t, monomialHom g⁻¹ (quaternarySeed t)∈quaternaryCode) :
    g.right∈binaryPermutationGroup := by
  intro d
  constructor
  · exact monomial_seed_residue g⁻¹ hi d
  · intro hd
    have h := monomial_seed_residue g hs (d ∘ g.right) hd
    simpa [Function.comp_def] using h

theorem monomial_code_preserves_of_seeds (g : SignedCoordinates Coordinate)
    (hp : g.right∈binaryPermutationGroup)
    (hs : ∀ t, monomialHom g (quaternarySeed t)∈quaternaryCode) :
    ∀ w, w∈quaternaryCode → monomialHom g w∈quaternaryCode := by
  apply quaternaryCode_le (quaternaryCode.comap (monomialHom g).toLinearMap)
  · intro b hb
    change monomialAction g (double b)∈quaternaryCode
    rw [monomialAction_double]
    exact quaternaryCode_double _ (binaryPermutation_torsion (⟨g.right,hp⟩ : binaryPermutationGroup)⁻¹ b hb)
  · exact hs

theorem monomial_mem_codeGroup_of_seed_images (g : SignedCoordinates Coordinate)
    (hs : ∀ t, monomialHom g (quaternarySeed t)∈quaternaryCode)
    (hi : ∀ t, monomialHom g⁻¹ (quaternarySeed t)∈quaternaryCode) : g∈codeGroup := by
  have hp := monomial_seed_permutation g hs hi
  intro w
  constructor
  · exact monomial_code_preserves_of_seeds g hp hs w
  · intro hw
    have hh := monomial_code_preserves_of_seeds g⁻¹ (binaryPermutationGroup.inv_mem hp) hi _ hw
    simpa using hh

theorem monomial_seed_permutation_of_forward (g : SignedCoordinates Coordinate)
    (hs : ∀ t, monomialHom g (quaternarySeed t)∈quaternaryCode) :
    g.right∈binaryPermutationGroup := by
  have hi := binaryPermutation_mem_of_preserves g.right.symm (monomial_seed_residue g hs)
  exact binaryPermutationGroup.inv_mem hi

theorem codeGroup_mem_of_preserves (g : SignedCoordinates Coordinate)
    (h : ∀ w, w∈quaternaryCode → monomialHom g w∈quaternaryCode) : g∈codeGroup := by
  let f : quaternaryCode → quaternaryCode := fun w => ⟨monomialHom g w.val,h w.val w.prop⟩
  have hf : Function.Injective f := by
    intro v w he
    exact Subtype.ext ((monomialHom g).injective (congrArg Subtype.val he))
  have hsurj := Finite.surjective_of_injective hf
  intro w
  constructor
  · exact h w
  · intro hw
    obtain ⟨v,hv⟩ := hsurj ⟨monomialHom g w,hw⟩
    have he : v.val=w := (monomialHom g).injective (congrArg Subtype.val hv)
    exact he ▸ v.prop

theorem monomial_mem_codeGroup_of_seeds (g : SignedCoordinates Coordinate)
    (hs : ∀ t, monomialHom g (quaternarySeed t)∈quaternaryCode) : g∈codeGroup :=
  codeGroup_mem_of_preserves g
    (monomial_code_preserves_of_seeds g (monomial_seed_permutation_of_forward g hs) hs)

end Atlas.Rudvalis

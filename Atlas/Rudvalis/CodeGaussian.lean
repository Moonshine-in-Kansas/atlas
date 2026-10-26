import Atlas.Rudvalis.CodeGroupGeneration
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem seedConjugateMonomial_commute (a b : SignedCoordinates SeedCoordinate)
    (h : a*b=b*a) : seedConjugateMonomial a*seedConjugateMonomial b=
      seedConjugateMonomial b*seedConjugateMonomial a := by
  apply monomialHom_injective
  rw [map_mul,map_mul]
  apply LinearEquiv.ext
  intro w
  obtain ⟨v,rfl⟩ := seedTransportLinear.surjective w
  change monomialHom (seedConjugateMonomial a)
    (monomialHom (seedConjugateMonomial b) (seedTransportLinear v))=
    monomialHom (seedConjugateMonomial b)
      (monomialHom (seedConjugateMonomial a) (seedTransportLinear v))
  simp only [seedConjugateMonomial_transport]
  have hh := congrArg (fun g => monomialHom g v) h
  simpa only [map_mul,LinearEquiv.mul_apply] using congrArg seedTransportLinear hh

private theorem seedP_I : seedPMonomial*seedUnitMonomial 4=
    seedUnitMonomial 4*seedPMonomial := by
  apply SemidirectProduct.ext
  · change (fun z => _)=(fun z => _)
    decide +kernel
  · ext z <;> decide +kernel +revert

private theorem seedRho_I : seedUnitMonomial 1*seedUnitMonomial 4=
    seedUnitMonomial 4*seedUnitMonomial 1 := by
  apply SemidirectProduct.ext
  · change (fun z => _)=(fun z => _)
    decide +kernel
  · ext z <;> decide +kernel +revert

private theorem seedSigma_I : seedUnitMonomial 2*seedUnitMonomial 4=
    seedUnitMonomial 4*seedUnitMonomial 2 := by
  apply SemidirectProduct.ext
  · change (fun z => _)=(fun z => _)
    decide +kernel
  · ext z <;> decide +kernel +revert

private theorem seedU_I : seedUMonomial*seedUnitMonomial 4=
    seedUnitMonomial 4*seedUMonomial := by
  apply SemidirectProduct.ext
  · change (fun z => _)=(fun z => _)
    decide +kernel
  · ext z <;> decide +kernel +revert

private theorem seedR_I : seedRMonomial*seedUnitMonomial 4=
    seedUnitMonomial 4*seedRMonomial := by
  apply SemidirectProduct.ext
  · change (fun z => _)=(fun z => _)
    decide +kernel
  · ext z <;> decide +kernel +revert

theorem codeP_commute_I : codeP*codeI=codeI*codeP :=
  Subtype.ext (seedConjugateMonomial_commute _ _ seedP_I)
theorem codeRho_commute_I : codeRho*codeI=codeI*codeRho :=
  Subtype.ext (seedConjugateMonomial_commute _ _ seedRho_I)
theorem codeSigma_commute_I : codeSigma*codeI=codeI*codeSigma :=
  Subtype.ext (seedConjugateMonomial_commute _ _ seedSigma_I)
theorem codeU_commute_I : codeU*codeI=codeI*codeU :=
  Subtype.ext (seedConjugateMonomial_commute _ _ seedU_I)
theorem codeR_commute_I : codeR*codeI=codeI*codeR :=
  Subtype.ext (seedConjugateMonomial_commute _ _ seedR_I)


theorem codeI_preserves_blocks (z : Coordinate) : (codeI.val.right z).1=z.1 := by
  have h := nineCodeGenerator_projection 0
  have hh := congrArg (fun g : binaryPermutationGroup => (g.val z).1) h
  exact hh

theorem codeKernel_commute_I (g : codeGroup) (hg : g∈codePermutationHom.ker) :
    g*codeI=codeI*g := by
  have hr : g.val.right=1 := (codePermutationHom_kernel g).mp hg
  have hs : g.val.left.toAdd∈signPatterns := by
    apply (codeGroup_sign_mem _).mp
    have he : (SemidirectProduct.inl g.val.left : SignedCoordinates Coordinate)=g.val := by
      apply SemidirectProduct.ext
      · rfl
      · exact hr.symm
    change SemidirectProduct.inl g.val.left∈codeGroup
    rw [he]
    exact g.prop
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change (fun z => g.val.left.toAdd z+codeI.val.left.toAdd (g.val.right.symm z))=
      (fun z => codeI.val.left.toAdd z+g.val.left.toAdd (codeI.val.right.symm z))
    funext z
    rw [hr]
    have hb : (codeI.val.right.symm z).1=z.1 := by
      have h := codeI_preserves_blocks (codeI.val.right.symm z)
      simpa using h.symm
    have he : g.val.left.toAdd (codeI.val.right.symm z)=g.val.left.toAdd z := by
      rw [show codeI.val.right.symm z=((codeI.val.right.symm z).1,
        (codeI.val.right.symm z).2) from rfl]
      rw [signPatterns_block_constant _ hs,hb]
      exact (signPatterns_block_constant _ hs z.1 z.2).symm
    change g.val.left.toAdd z+codeI.val.left.toAdd z=
      codeI.val.left.toAdd z+g.val.left.toAdd (codeI.val.right.symm z)
    rw [he]
    exact add_comm _ _
  · change g.val.right*codeI.val.right=codeI.val.right*g.val.right
    rw [hr,one_mul,mul_one]

theorem codeGroup_commute_I (g : codeGroup) : g*codeI=codeI*g := by
  have htop : Subgroup.centralizer ({codeI} : Set codeGroup)=⊤ := by
    apply codeGroup_eq_top_of_generators
    · intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mpr (codeKernel_commute_I h hh)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr codeP_commute_I
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr codeRho_commute_I
    · exact Subgroup.mem_centralizer_singleton_iff.mpr codeSigma_commute_I
    · exact Subgroup.mem_centralizer_singleton_iff.mpr codeU_commute_I
    · exact Subgroup.mem_centralizer_singleton_iff.mpr codeR_commute_I
  apply Subgroup.mem_centralizer_singleton_iff.mp
  rw [htop]
  trivial

theorem codeGroup_gaussian_linear (g : codeGroup) (w : QuaternaryWord) :
    monomialHom g.val (monomialHom codeI.val w)=
      monomialHom codeI.val (monomialHom g.val w) := by
  have h := congrArg (fun a : codeGroup => monomialHom a.val w) (codeGroup_commute_I g)
  change monomialHom (g.val*codeI.val) w=monomialHom (codeI.val*g.val) w at h
  simpa only [map_mul,LinearEquiv.mul_apply] using h

theorem codeI_square_action (w : QuaternaryWord) :
    monomialHom codeI.val (monomialHom codeI.val w) = -w := by
  obtain ⟨v,rfl⟩ := seedTransportLinear.surjective w
  change monomialHom (seedConjugateMonomial (seedUnitMonomial 4))
    (monomialHom (seedConjugateMonomial (seedUnitMonomial 4)) (seedTransportLinear v))=_
  simp only [seedConjugateMonomial_transport,seedUnitMonomial_apply]
  change seedTransportLinear (seedIOperator (seedIOperator v)) = _
  rw [seedI_square,map_neg]

end Atlas.Rudvalis



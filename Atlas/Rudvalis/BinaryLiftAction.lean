import Atlas.Rudvalis.BinaryLinearLifts

/-! Actual coordinate lifts of linear changes of Fano coordinates. -/
namespace Atlas.Rudvalis

noncomputable def rowTranslationPerm (t : Point → E) : Equiv.Perm Coordinate where
  toFun z := (z.1,z.2+t z.1)
  invFun z := (z.1,z.2+t z.1)
  left_inv z := by simp [add_assoc,vector_add_self]
  right_inv z := by simp [add_assoc,vector_add_self]

noncomputable def binarySectionLift (A : E ≃ₗ[Bit] E) (t : Point → E) : Equiv.Perm Coordinate :=
  (rowTranslationPerm t).trans (Equiv.prodCongr (linearPointEquiv A) A.toEquiv)

theorem binarySectionLift_apply (A : E ≃ₗ[Bit] E) (t : Point → E) (p : Point) (x : E) :
    binarySectionLift A t (p,x)=(linearPointEquiv A p,A (x+t p)) := rfl

noncomputable def binaryLinearMatrix (A : E ≃ₗ[Bit] E) : BinaryMatrix :=
  LinearMap.toMatrix' A.toLinearMap

theorem binaryLinearMatrix_apply (A : E ≃ₗ[Bit] E) (x : E) :
    matrixAt (binaryLinearMatrix A) x=A x := LinearMap.toMatrix'_mulVec _ _

theorem matrixAt_mul (M N : BinaryMatrix) (x : E) :
    matrixAt (M*N) x=matrixAt M (matrixAt N x) := (Matrix.mulVec_mulVec _ _ _).symm

noncomputable def pullbackBinaryMatrix (A : E ≃ₗ[Bit] E) (M : BinaryMatrix) : BinaryMatrix :=
  (binaryLinearMatrix A).transpose * M * binaryLinearMatrix A

theorem pullbackBinaryMatrix_pair (A : E ≃ₗ[Bit] E) (M : BinaryMatrix) (p x : E) :
    dot (matrixAt (pullbackBinaryMatrix A M) p) x=dot (matrixAt M (A p)) (A x) := by
  rw [pullbackBinaryMatrix,matrixAt_mul,matrixAt_mul,binaryLinearMatrix_apply]
  rw [← matrixAt_transpose_pair,binaryLinearMatrix_apply,dot_comm]

theorem theta_section_corrected (A : E ≃ₗ[Bit] E) (t : Point → E)
    (ht : ∀ p c x, theta (linearPointEquiv A p) (A c) (A x)+theta p c x=polar c (t p) x)
    (p : Point) (c x : E) :
    theta (linearPointEquiv A p) (A c) (A (x+t p))=theta p c x+theta p c (t p) := by
  have h := ht p c (x+t p)
  rw [theta_translate] at h
  have hp : polar c (t p) (x+t p)=polar c (t p) x := by
    simp [polar]
    ring_nf
    have htwo : (2 : Bit)=0 := by decide
    simp [htwo]
  rw [hp] at h
  have hh : ∀ a b d e : Bit, a+(b+d+e)=e → a=b+d := by decide
  exact hh _ _ _ _ h

noncomputable def sectionPullbackParameters (A : E ≃ₗ[Bit] E) (t : Point → E)
    (a : BinaryParameters) : BinaryParameters :=
  (fun p => a.1 (linearPointEquiv A p)+dot (matrixAt a.2.1 (A p.val)) (A (t p))+
    theta p (A.symm a.2.2) (t p),pullbackBinaryMatrix A a.2.1,A.symm a.2.2)

theorem binaryNormalMap_sectionPullback (A : E ≃ₗ[Bit] E) (t : Point → E)
    (ht : ∀ p c x, theta (linearPointEquiv A p) (A c) (A x)+theta p c x=polar c (t p) x)
    (a : BinaryParameters) :
    binaryNormalMap (sectionPullbackParameters A t a)=binaryNormalMap a ∘ binarySectionLift A t := by
  funext z
  rcases z with ⟨p,x⟩
  change (a.1 (linearPointEquiv A p)+dot (matrixAt a.2.1 (A p.val)) (A (t p))+
    theta p (A.symm a.2.2) (t p))+
    dot (matrixAt (pullbackBinaryMatrix A a.2.1) p.val) x+theta p (A.symm a.2.2) x =
    a.1 (linearPointEquiv A p)+dot (matrixAt a.2.1 (A p.val)) (A (x+t p))+
      theta (linearPointEquiv A p) a.2.2 (A (x+t p))
  have he := theta_section_corrected A t ht p (A.symm a.2.2) x
  rw [A.apply_symm_apply] at he
  rw [he,map_add,dot_add_right,pullbackBinaryMatrix_pair]
  ring

theorem binaryPermutation_mem_of_preserves (g : Equiv.Perm Coordinate)
    (hg : ∀ w : BinaryWord, w∈binaryResidue → w ∘ g ∈ binaryResidue) :
    g∈binaryPermutationGroup := by
  let f : binaryResidue → binaryResidue := fun w => ⟨w.val ∘ g,hg w.val w.prop⟩
  have hi : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    funext x
    have hh := congrFun (congrArg Subtype.val he) (g.symm x)
    simpa [f,Function.comp_def] using hh
  have hs := Finite.surjective_of_injective hi
  intro w
  refine ⟨hg w,?_⟩
  intro hw
  obtain ⟨v,hv⟩ := hs ⟨w ∘ g,hw⟩
  have he : v.val=w := by
    funext x
    have hh := congrFun (congrArg Subtype.val hv) (g.symm x)
    simpa [f,Function.comp_def] using hh
  exact he ▸ v.prop

theorem binarySectionLift_mem (A : E ≃ₗ[Bit] E) (t : Point → E)
    (ht : ∀ p c x, theta (linearPointEquiv A p) (A c) (A x)+theta p c x=polar c (t p) x) :
    binarySectionLift A t∈binaryPermutationGroup := by
  apply binaryPermutation_mem_of_preserves
  rintro w ⟨a,rfl⟩
  exact ⟨sectionPullbackParameters A t a,binaryNormalMap_sectionPullback A t ht a⟩

noncomputable def binarySectionGroupLift (A : E ≃ₗ[Bit] E) (t : Point → E)
    (ht : ∀ p c x, theta (linearPointEquiv A p) (A c) (A x)+theta p c x=polar c (t p) x) :
    binaryPermutationGroup := ⟨binarySectionLift A t,binarySectionLift_mem A t ht⟩

theorem binarySectionGroupLift_blocks (A : E ≃ₗ[Bit] E) (t : Point → E)
    (ht : ∀ p c x, theta (linearPointEquiv A p) (A c) (A x)+theta p c x=polar c (t p) x) :
    binaryBlockLinearHom (binarySectionGroupLift A t ht)=A := by
  apply LinearEquiv.ext
  intro x
  by_cases hx : x=0
  · simp [hx]
  · let p : Point := ⟨x,hx⟩
    have h := binaryBlockPermutation_coordinates (binarySectionGroupLift A t ht) (p,0)
    have he := binaryBlockLinearEquiv_point (binarySectionGroupLift A t ht) p
    change binaryBlockLinearEquiv (binarySectionGroupLift A t ht) p.val=A p.val
    rw [he]
    exact congrArg Subtype.val h.symm

theorem binaryBlockLinearHom_surjective : Function.Surjective binaryBlockLinearHom := by
  intro A
  choose t ht using section_difference_origin A
  exact ⟨binarySectionGroupLift A t ht,binarySectionGroupLift_blocks A t ht⟩

end Atlas.Rudvalis

import Atlas.Fischer.SemilinearGeneratedConjugation
import Atlas.Fischer.GeneratedFullFrameStabilizer

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Recover a literal basic-ray frame permutation from the induced conjugation
of its twenty-four distinguished involutions. -/
theorem semilinear_mem_basicFrame_of_class_image (e : SemilinearAlgebraAutomorphism)
    (he : semilinearGeneratedConjugation e '' standardCommutingFrame ⊆ standardCommutingFrame) :
    e ∈ basicFrameStabilizer := by
  classical
  have hj (i : Omega) : ∃ j : Omega,
      rootRay (e.val (basicAxis i))=rootRay (basicAxis j) := by
    have hi := he ⟨distinguishedRootElement (.inl i),⟨i,rfl⟩,rfl⟩
    obtain ⟨j,hj⟩ := hi
    obtain ⟨s,hs⟩ := reflectingRootParameter_automorphism e (.inl i)
    have hd := semilinearGeneratedConjugation_parameter e (.inl i) s hs
    have ht : s=.inl j := distinguishedRootElement_injective (hd.symm.trans hj.symm)
    rw [ht] at hs
    exact ⟨j,hs⟩
  choose σ hσ using hj
  have hact (i : Omega) : semilinearDisplayedRayAction e (displayedRayOfParameter (.inl i))=
      displayedRayOfParameter (.inl (σ i)) := by
    apply Subtype.ext
    rw [semilinearDisplayedRayAction_parameter_value]
    exact hσ i
  have hinj : Function.Injective σ := by
    intro i j hij
    have hh : semilinearDisplayedRayAction e (displayedRayOfParameter (.inl i))=
        semilinearDisplayedRayAction e (displayedRayOfParameter (.inl j)) := by
      rw [hact,hact,hij]
    exact basicAxis_ray_injective (congrArg Subtype.val ((semilinearDisplayedRayAction e).injective hh))
  exact ⟨Equiv.ofBijective σ ⟨hinj,Finite.surjective_of_injective hinj⟩,hσ⟩

end Atlas.Fischer

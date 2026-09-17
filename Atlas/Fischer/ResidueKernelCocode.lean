import Atlas.Fischer.ResidueAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def residueBasicPoint (S : Finset Omega) (i : Omega) (hi : i ∉ S) : ResiduePoint S :=
  ⟨distinguishedRootElement (.inl i),⟨.inl i,rfl⟩,by
    rintro ⟨j,hj,he⟩
    have hji := Sum.inl.inj (distinguishedRootElement_injective he)
    exact hi (hji ▸ hj),
    fun j _ => standardCommutingFrame_isFrame.2.1 _ ⟨j,rfl⟩ _ ⟨i,rfl⟩⟩

/-- A residue-kernel element fixes the entire marked frame, including the
marked elements centralized by definition. -/
theorem residueAction_kernel_basic_frame (S : Finset Omega) (g : residueCentralizer S)
    (hg : g ∈ (residueConjugationHom S).ker) : g.val ∈ basicFramePointwiseRayStabilizer := by
  rintro x ⟨i,rfl⟩
  have hh : g.val * distinguishedRootElement (.inl i) * g.val⁻¹ =
      distinguishedRootElement (.inl i) := by
    by_cases hi : i ∈ S
    · exact (mem_markedPentadPointwise_iff S g.val).mp g.property i hi
    · exact (mem_residueAction_kernel_iff S g).mp hg (residueBasicPoint S i hi)
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

theorem residueAction_kernel_cocode (S : Finset Omega) (g : residueCentralizer S)
    (hg : g ∈ (residueConjugationHom S).ker) :
    ∃ d : Multiplicative Cocode, g.val = generatedCocodeRayHom d := by
  have h := residueAction_kernel_basic_frame S g hg
  rw [basicFramePointwiseRayStabilizer_eq_cocode] at h
  obtain ⟨d,hd⟩ := h
  exact ⟨d,hd.symm⟩

end Atlas.Fischer

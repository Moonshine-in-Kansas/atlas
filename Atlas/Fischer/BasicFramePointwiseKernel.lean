import Atlas.Fischer.StandardFrameRayStabilizer
import Atlas.Fischer.GeneratedRayCocode

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual pointwise conjugation stabilizer of the marked basic frame. -/
def basicFramePointwiseRayStabilizer : Subgroup rootGeneratedRayGroup :=
  Subgroup.centralizer standardCommutingFrame

/-- The same subgroup is literally the kernel of the action on every basic ray. -/
theorem mem_basicFramePointwiseRayStabilizer_iff (g : rootGeneratedRayGroup) :
    g ∈ basicFramePointwiseRayStabilizer ↔ ∀ i : Omega,
      g.val (displayedRayOfParameter (.inl i))=displayedRayOfParameter (.inl i) := by
  constructor
  · intro hg i
    obtain ⟨t,ht⟩ := displayedRayOfParameter_surjective (g.val (displayedRayOfParameter (.inl i)))
    have hc := distinguishedRootElement_conjugation g (.inl i) t ht.symm
    have hcomm := hg (distinguishedRootElement (.inl i)) ⟨i,rfl⟩
    have he : g*distinguishedRootElement (.inl i)*g⁻¹=distinguishedRootElement (.inl i) :=
      mul_inv_eq_iff_eq_mul.mpr hcomm.symm
    have hti : t=.inl i := distinguishedRootElement_injective (hc.symm.trans he)
    rw [hti] at ht
    exact ht.symm
  · intro hg
    rintro x ⟨i,rfl⟩
    have hc := distinguishedRootElement_conjugation g (.inl i) (.inl i) (hg i)
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm

/-- Restrict the existing faithful cocode ray action to its proved generated
ambient group, retaining exactly the same permutations. -/
def generatedCocodeRayHom : Multiplicative Cocode →* rootGeneratedRayGroup :=
  cocodeRayHom.codRestrict rootGeneratedRayGroup (fun d => cocodeRayHom_range_le ⟨d,rfl⟩)

theorem generatedCocodeRayHom_parker (d : Multiplicative Cocode) :
    generatedCocodeRayHom d=parkerRayHom (parkerCocodeEmbedding d) := rfl

/-- Literal pointwise frame-kernel equality, proved by the full Parker frame
stabilizer and its actual coordinate projection kernel. -/
theorem basicFramePointwiseRayStabilizer_eq_cocode :
    basicFramePointwiseRayStabilizer=generatedCocodeRayHom.range := by
  apply le_antisymm
  · intro g hg
    have hf : g ∈ standardFrameRayStabilizer :=
      Subgroup.centralizer_le_normalizer standardCommutingFrame hg
    rw [← parkerRayHom_range] at hf
    obtain ⟨h,rfl⟩ := hf
    have hp : parkerStandardProjection h=1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      apply (parkerRayHom_commutes_basic_iff h i).mp
      exact (hg _ ⟨i,rfl⟩).symm
    have hk : h ∈ parkerCocodeEmbedding.range := by
      rw [parkerCocodeEmbedding_range]
      exact hp
    obtain ⟨d,rfl⟩ := hk
    exact ⟨d,generatedCocodeRayHom_parker d⟩
  · rintro g ⟨d,rfl⟩
    rintro x ⟨i,rfl⟩
    rw [generatedCocodeRayHom_parker]
    have hp : parkerStandardProjection (parkerCocodeEmbedding d)=1 := by
      have hm : parkerCocodeEmbedding d ∈ parkerCocodeEmbedding.range := ⟨d,rfl⟩
      rw [parkerCocodeEmbedding_range] at hm
      exact hm
    have hc := (parkerRayHom_commutes_basic_iff (parkerCocodeEmbedding d) i).mpr (by rw [hp]; rfl)
    exact hc.eq.symm

/-- The same equality in the original ambient permutation group. -/
theorem basicFramePointwiseRayStabilizer_ambient :
    basicFramePointwiseRayStabilizer.map rootGeneratedRayGroup.subtype=cocodeRayHom.range := by
  rw [basicFramePointwiseRayStabilizer_eq_cocode]
  apply le_antisymm
  · rintro x ⟨g,⟨d,rfl⟩,rfl⟩
    exact ⟨d,rfl⟩
  · rintro x ⟨d,rfl⟩
    exact ⟨generatedCocodeRayHom d,⟨d,rfl⟩,rfl⟩

theorem basicFramePointwiseRayStabilizer_order :
    Nat.card basicFramePointwiseRayStabilizer=4096 := by
  rw [basicFramePointwiseRayStabilizer_eq_cocode,
    ← Nat.card_congr (MonoidHom.ofInjective (show Function.Injective generatedCocodeRayHom from
      fun a b h => cocodeRayHom_injective (congrArg Subtype.val h))).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative Cocode ≃ Cocode),cocode_card]

end Atlas.Fischer

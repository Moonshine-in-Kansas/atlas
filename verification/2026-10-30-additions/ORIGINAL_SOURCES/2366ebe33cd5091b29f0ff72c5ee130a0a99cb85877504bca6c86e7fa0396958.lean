import Atlas.LinearGroups.ReeF4.OppositePairTensorPreservation
import Atlas.LinearGroups.ReeF4.OppositePairRestrictionFaithful
import Atlas.LinearGroups.SuzukiFamily.TensorDiagonal
import Atlas.LinearGroups.SuzukiFamily.TensorAction

/-! The reverse inclusion for the full opposite-VECTOR stabilizer.
The generated Suzuki model is recognized using the actual induced tensor,
including q=2. No order or simplicity theorem is imported. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem restriction_preserves_suzuki_tensor {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (g : Model F m)
    (he : g.val (rootVector (0,0))=rootVector (0,0))
    (hf : g.val (rootVector (0,7))=rootVector (0,7)) :
    Atlas.SuzukiFamily.PreservesPartialTensor m (oppositePairLinearRestriction g he hf) := by
  intro u v huv
  have h := oppositePairLinearRestriction_tensor g he hf u v huv
  rw [thetaInv_eq_symm hcard] at h
  exact h

private theorem restriction_mul_suzuki {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (s : Atlas.SuzukiFamily.Group F m)
    (g : Model F m)
    (he : g.val (rootVector (0,0))=rootVector (0,0))
    (hf : g.val (rootVector (0,7))=rootVector (0,7))
    (ke : (modelSuzukiEmbedding m hcard s*g).val (rootVector (0,0))=rootVector (0,0))
    (kf : (modelSuzukiEmbedding m hcard s*g).val (rootVector (0,7))=rootVector (0,7))
    (v : Fin 4 → F) :
    oppositePairLinearRestriction (modelSuzukiEmbedding m hcard s*g) ke kf v =
      Atlas.SuzukiFamily.columnEquiv s.val (oppositePairLinearRestriction g he hf v) := by
  change suzukiLeviBlockProject 1
    ((modelSuzukiEmbedding m hcard s).val (g.val (suzukiLeviBlockEmbed 1 v))) = _
  rw [←oppositePairLinearRestriction_embed g he hf v]
  exact modelSuzukiEmbedding_restriction_apply hcard s _

/-- Every full intrinsic automorphism fixing the two opposite vectors is an
actual element of the constructed Suzuki subgroup. -/
theorem oppositeVectorStabilizer_eq_suzuki {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (g : Model F m)
    (he : g.val (rootVector (0,0))=rootVector (0,0))
    (hf : g.val (rootVector (0,7))=rootVector (0,7)) :
    ∃ s : Atlas.SuzukiFamily.Group F m, g=modelSuzukiEmbedding m hcard s := by
  let R := oppositePairLinearRestriction g he hf
  have hB : ∀ u v, Atlas.SuzukiFamily.tensorPolar (R u) (R v)=
      Atlas.SuzukiFamily.tensorPolar u v := oppositePairLinearRestriction_polar g he hf
  have hT : Atlas.SuzukiFamily.PreservesPartialTensor m R :=
    restriction_preserves_suzuki_tensor hcard g he hf
  obtain ⟨s,a,d,hs0,hs3⟩ := Atlas.SuzukiFamily.tensor_pair_normalization hcard R hB hT
  let k : Model F m := modelSuzukiEmbedding m hcard s*g
  have ke : k.val (rootVector (0,0))=rootVector (0,0) := by
    change (modelSuzukiEmbedding m hcard s).val (g.val (rootVector (0,0))) = _
    rw [he,modelSuzukiEmbedding_fixes_first hcard s]
  have kf : k.val (rootVector (0,7))=rootVector (0,7) := by
    change (modelSuzukiEmbedding m hcard s).val (g.val (rootVector (0,7))) = _
    rw [hf,modelSuzukiEmbedding_fixes_opposite hcard s]
  let K := oppositePairLinearRestriction k ke kf
  have hK (v : Fin 4 → F) : K v=Atlas.SuzukiFamily.columnEquiv s.val (R v) :=
    restriction_mul_suzuki hcard s g he hf ke kf v
  have hk0 : K (Atlas.SuzukiFamily.tensorBasis 0)=a • Atlas.SuzukiFamily.tensorBasis 0 := by
    rw [hK]
    exact hs0
  have hk3 : K (Atlas.SuzukiFamily.tensorBasis 3)=d • Atlas.SuzukiFamily.tensorBasis 3 := by
    rw [hK]
    exact hs3
  have hKB : ∀ u v, Atlas.SuzukiFamily.tensorPolar (K u) (K v)=
      Atlas.SuzukiFamily.tensorPolar u v := oppositePairLinearRestriction_polar k ke kf
  have hKT : Atlas.SuzukiFamily.PreservesPartialTensor m K :=
    restriction_preserves_suzuki_tensor hcard k ke kf
  obtain ⟨t,ht⟩ := Atlas.SuzukiFamily.tensor_linear_diagonal_reduction m K a d hk0 hk3 hKB hKT
  let st : Atlas.SuzukiFamily.Group F m :=
    ⟨Atlas.SuzukiFamily.torusElement m t,Atlas.SuzukiFamily.torusElement_mem m t⟩
  have hk : k=modelSuzukiEmbedding m hcard st := by
    apply eq_modelSuzukiEmbedding_of_restriction hcard k ke kf st
    intro v
    change K v=Atlas.SuzukiFamily.matrix (Atlas.SuzukiFamily.torusElement m t) *ᵥ v
    rw [Atlas.SuzukiFamily.matrix_torus]
    exact ht v
  refine ⟨s⁻¹*st,?_⟩
  calc
    g = (modelSuzukiEmbedding m hcard s)⁻¹ * k := by dsimp only [k]; group
    _ = (modelSuzukiEmbedding m hcard s)⁻¹ * modelSuzukiEmbedding m hcard st := by rw [hk]
    _ = modelSuzukiEmbedding m hcard (s⁻¹*st) := by rw [map_mul,map_inv]

end Atlas.ReeF4

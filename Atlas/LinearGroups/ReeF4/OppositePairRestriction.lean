import Atlas.LinearGroups.ReeF4.OppositePairIntrinsicSpace
import Atlas.LinearGroups.ReeF4.IntrinsicGroup

/-! Canonical restriction of the vectorwise opposite-pair
stabilizer to its intrinsic Suzuki four-space. No recognition conclusion. -/
noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem opposite_model_cross {m : ℕ} (g : Model F m) (u v : TraceZero F) :
    g.val (traceZeroCross u v) = traceZeroCross (g.val u) (g.val v) := by
  obtain ⟨hp,_⟩ := (mem_modelSubgroup_iff m g.val).mp g.property
  exact (traceZeroCross_of_forms g.val
    (traceZeroStabilizer_quadratic ⟨g.val,hp⟩)
    (traceZeroStabilizer_cubic ⟨g.val,hp⟩) u v).symm

private theorem opposite_model_diagonal {m : ℕ} (g : Model F m)
    (he : g.val (rootVector (0,0))=rootVector (0,0))
    (hf : g.val (rootVector (0,7))=rootVector (0,7)) :
    g.val (diagonalVector 0)=diagonalVector 0 := by
  have h := opposite_model_cross g (rootVector (0,0)) (rootVector (0,7))
  rw [he,hf] at h
  have hc : traceZeroCross (rootVector (F := F) (0,0)) (rootVector (0,7)) =
      diagonalVector 0 := rootCross_opposite (0,0)
  rw [hc] at h
  exact h

/-- The actual full Model preserves the intrinsic four-space whenever both
marked opposite vectors are fixed. -/
theorem oppositePair_preserves_negativeBlock {m : ℕ} (g : Model F m)
    (he : g.val (rootVector (0,0))=rootVector (0,0))
    (hf : g.val (rootVector (0,7))=rootVector (0,7))
    {z : TraceZero F} (hz : z ∈ LinearMap.range (suzukiLeviBlockEmbed (F := F) 1)) :
    g.val z ∈ LinearMap.range (suzukiLeviBlockEmbed (F := F) 1) := by
  obtain ⟨hp,hg⟩ := (mem_modelSubgroup_iff m g.val).mp g.property
  obtain ⟨w,hd,rfl⟩ := (mem_negativeSuzukiBlock_iff_intrinsicImage (thetaInv F m) z).mp hz
  have hdg : StarDomain (g.val (rootVector (0,0))) (g.val w) :=
    (starDomain_polynomialStabilizer_iff ⟨g.val,hp⟩ _ _).mpr hd
  have hd' : StarDomain (rootVector (0,0)) (g.val w) := by simpa only [he] using hdg
  have hs := hg (rootVector (0,0)) w hd
  have hs' : proposedPartialProduct (thetaInv F m).toRingHom
      (rootVector (0,0)) (g.val w) hd' =
      g.val (proposedPartialProduct (thetaInv F m).toRingHom (rootVector (0,0)) w hd) := by
    simpa only [he] using hs
  apply (mem_negativeSuzukiBlock_iff_intrinsicImage (thetaInv F m) _).mpr
  refine ⟨g.val w,hd',?_⟩
  rw [hs',opposite_model_cross,opposite_model_diagonal g he hf]

private theorem negativeBlock_embed_project {z : TraceZero F}
    (hz : z ∈ LinearMap.range (suzukiLeviBlockEmbed (F := F) 1)) :
    suzukiLeviBlockEmbed 1 (suzukiLeviBlockProject 1 z)=z := by
  obtain ⟨v,rfl⟩ := hz
  rw [suzukiLeviBlockProject_embed]

private theorem opposite_fixed_inv {m : ℕ} (g : Model F m) {z : TraceZero F}
    (hz : g.val z=z) : (g⁻¹).val z=z := by
  change g.val.symm z=z
  exact (congrArg g.val.symm hz).symm.trans (g.val.symm_apply_apply z)

/-- Actual coordinate restriction, with inverse provided by the inverse Model
operator. This does not yet assert membership in the generated Suzuki group. -/
def oppositePairLinearRestriction {m : ℕ} (g : Model F m)
    (he : g.val (rootVector (0,0))=rootVector (0,0))
    (hf : g.val (rootVector (0,7))=rootVector (0,7)) :
    (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) where
  toFun v := suzukiLeviBlockProject 1 (g.val (suzukiLeviBlockEmbed 1 v))
  invFun v := suzukiLeviBlockProject 1 ((g⁻¹).val (suzukiLeviBlockEmbed 1 v))
  left_inv v := by
    dsimp only
    rw [negativeBlock_embed_project
      (oppositePair_preserves_negativeBlock g he hf ⟨v,rfl⟩)]
    change suzukiLeviBlockProject 1 (g.val.symm (g.val (suzukiLeviBlockEmbed 1 v)))=v
    rw [LinearEquiv.symm_apply_apply,suzukiLeviBlockProject_embed]
  right_inv v := by
    dsimp only
    rw [negativeBlock_embed_project
      (oppositePair_preserves_negativeBlock g⁻¹ (opposite_fixed_inv g he)
        (opposite_fixed_inv g hf) ⟨v,rfl⟩)]
    change suzukiLeviBlockProject 1 (g.val (g.val.symm (suzukiLeviBlockEmbed 1 v)))=v
    rw [LinearEquiv.apply_symm_apply,suzukiLeviBlockProject_embed]
  map_add' u v := by simp only [_root_.map_add]
  map_smul' a v := by simp only [map_smul,RingHom.id_apply]

theorem oppositePairLinearRestriction_embed {m : ℕ} (g : Model F m)
    (he : g.val (rootVector (0,0))=rootVector (0,0))
    (hf : g.val (rootVector (0,7))=rootVector (0,7)) (v : Fin 4 → F) :
    suzukiLeviBlockEmbed 1 (oppositePairLinearRestriction g he hf v)=
      g.val (suzukiLeviBlockEmbed 1 v) :=
  negativeBlock_embed_project (oppositePair_preserves_negativeBlock g he hf ⟨v,rfl⟩)
end Atlas.ReeF4

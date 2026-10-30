import Atlas.LinearGroups.ReeF4.SuzukiNaturalVectorFixer
import Atlas.LinearGroups.ReeF4.PositiveMarkedLineAction
import Atlas.LinearGroups.ReeF4.TailLeviNormalization
import Atlas.LinearGroups.ReeF4.RootSuzukiScalarPair

/-!
Source-only, uncompiled. Exact natural-block and extremal-coordinate arguments
remove the scalar and shear in a positive-times-Suzuki Levi factorization.
The actual Suzuki natural-vector fixer then lands in the first positive short
root subgroup, with the retained parameter shear b + a*theta(a).
-/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem suzukiLeviHom_naturalBlock (s : Atlas.Symplectic.Sp 2 F)
    (k : Fin 4) (w : TraceZero F) :
    suzukiLeviBlockProject k (suzukiLeviHom s w) =
      SuzukiFamily.matrix s *ᵥ suzukiLeviBlockProject k w := by
  change suzukiLeviBlockProject k (suzukiLeviLinear (SuzukiFamily.matrix s) w) = _
  exact congrArg (fun x : SuzukiLeviCoordinates F => x.1 k)
    (suzukiLeviLinear_coordinates (SuzukiFamily.matrix s) w)

/-- e2 is the last vector of natural block 1, hence the retained infinityVector. -/
theorem suzukiLeviBlockProject_secondRoot :
    suzukiLeviBlockProject 1 (rootVector (F := F) (2,0)) =
      SuzukiFamily.infinityVector := by
  funext i
  fin_cases i <;>
    simp [suzukiLeviBlockProject, suzukiLeviBlockLabel, rootVector,
      Pi.single_apply, SuzukiFamily.infinityVector]

theorem modelSuzukiEmbedding_mem_positiveRootSubgroup_of_fix_secondRoot {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (s : SuzukiFamily.Group F m)
    (hfix : (modelSuzukiEmbedding m hcard s).val (rootVector (F := F) (2,0)) =
      rootVector (2,0)) :
    modelSuzukiEmbedding m hcard s ∈ positiveRootSubgroup hcard := by
  have hnat := congrArg (suzukiLeviBlockProject (F := F) 1) hfix
  change suzukiLeviBlockProject 1 (suzukiLeviHom s.val (rootVector (2,0))) =
    suzukiLeviBlockProject 1 (rootVector (2,0)) at hnat
  rw [suzukiLeviHom_naturalBlock] at hnat
  simp only [suzukiLeviBlockProject_secondRoot] at hnat
  obtain ⟨a,b,hs⟩ := (suzuki_infinityVector_fixer_iff_root hcard s).mp hnat
  have he : modelSuzukiEmbedding m hcard s =
      shortRootModelEmbedding hcard (shortRootParameters m hcard (a,b+a*theta F m a)) := by
    apply Subtype.ext
    change suzukiLeviHom s.val = shortRootPairEquiv m hcard a (b+a*theta F m a)
    rw [hs, suzukiLeviHom_root_unshear]
  rw [he, ← alternatingShortRootHom_zero_eq]
  exact alternatingShortRoot_mem_positiveRootSubgroup hcard 0 _

/-- Exact e0 fixation kills the scalar because its weight is theta(c). -/
theorem suzukiProduct_scalar_eq_one_of_positive_product_fix_firstRoot {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (r : positiveRootSubgroup hcard)
    (s : SuzukiFamily.Group F m) (c : Fˣ)
    (hfix : (r.val * modelSuzukiProductHom hcard (s,c)).val
      (rootVector (F := F) (0,0)) = rootVector (0,0)) : c = 1 := by
  change r.val.val ((modelSuzukiProductHom hcard (s,c)).val
    (rootVector (F := F) (0,0))) = rootVector (0,0) at hfix
  rw [modelSuzukiProduct_first_root, _root_.map_smul,
    positiveRootSubgroup_fixes_lowestRoot hcard r] at hfix
  have hc : ((thetaUnits m c : Fˣ) : F) = 1 := by
    simpa [rootVector, Pi.single_apply, smul_eq_mul] using
      congrArg (fun w : TraceZero F => w.val.2 0 0) hfix
  apply Units.ext
  apply (theta F m).injective
  change theta F m (c : F) = theta F m (1 : F)
  change theta F m (c : F) = 1 at hc
  simpa only [map_one] using hc

/-- The Suzuki representation preserves the e0 coefficient, so its residual shear vanishes. -/
theorem modelSuzukiEmbedding_fix_second_of_positive_product_fix_second {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (r : positiveRootSubgroup hcard)
    (s : SuzukiFamily.Group F m)
    (hfix : (r.val * modelSuzukiEmbedding m hcard s).val
      (rootVector (F := F) (2,0)) = rootVector (2,0)) :
    (modelSuzukiEmbedding m hcard s).val (rootVector (F := F) (2,0)) =
      rootVector (2,0) := by
  let a : F := (r.val.val.symm (rootVector (F := F) (2,0))).val.2 0 0
  have hshear : r.val.val.symm (rootVector (F := F) (2,0)) =
      a • rootVector (0,0) + rootVector (2,0) :=
    (positiveRootSubgroup_le_unitriangular hcard
      ((positiveRootSubgroup hcard).inv_mem r.property)).markedLine_second
  have he : (modelSuzukiEmbedding m hcard s).val (rootVector (F := F) (2,0)) =
      r.val.val.symm (rootVector (2,0)) := by
    have hh := congrArg r.val.val.symm hfix
    change r.val.val.symm (r.val.val
      ((modelSuzukiEmbedding m hcard s).val (rootVector (2,0)))) =
        r.val.val.symm (rootVector (2,0)) at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh
  have ha : a = 0 := by
    have hc := congrArg (fun w : TraceZero F => w.val.2 0 0) (he.trans hshear)
    change (suzukiLeviHom s.val (rootVector (F := F) (2,0))).val.2 0 0 =
      (a • rootVector (0,0) + rootVector (2,0)).val.2 0 0 at hc
    rw [suzukiLeviHom_negative_coordinate] at hc
    simpa [rootVector, Pi.single_apply, smul_eq_mul] using hc.symm
  simpa only [ha, zero_smul, zero_add] using he.trans hshear

end Atlas.ReeF4

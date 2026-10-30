import Atlas.LinearGroups.ReeF4.SpecialOppositeAction
import Atlas.LinearGroups.ReeF4.RootSuzukiScalarPair

/-! Normalize an arbitrary ordered opposite-point stabilizer to one fixing
the two actual marked vectors. No identification of the remaining stabilizer. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem model_opposite_pair_scalars {m : ℕ} (g : Model F m)
    (he : g • firstSpecialPoint (F := F) m = firstSpecialPoint m)
    (hf : g • oppositeSpecialPoint (F := F) m = oppositeSpecialPoint m) :
    ∃ a : Fˣ,
      g.val (rootVector (0,0)) = (a : F) • rootVector (0,0) ∧
      g.val (rootVector (0,7)) = ((a⁻¹ : Fˣ) : F) • rootVector (0,7) := by
  rw [firstSpecialPoint,specialPointMk_smul] at he
  rw [oppositeSpecialPoint,specialPointMk_smul] at hf
  obtain ⟨a,ha⟩ := (specialPointMk_eq_iff m _ _ _ _).mp he
  obtain ⟨b,hb⟩ := (specialPointMk_eq_iff m _ _ _ _).mp hf
  have hpol := model_preserves_polar g (rootVector (0,0)) (rootVector (0,7))
  rw [← ha,← hb] at hpol
  simp only [Units.smul_def,traceZeroPolar_smul_left] at hpol
  rw [traceZeroPolar_comm,traceZeroPolar_smul_left,
    traceZeroPolar_comm,first_opposite_polar,mul_one] at hpol
  have hab : a*b=1 := Units.ext hpol
  have hb' : b=a⁻¹ := eq_inv_of_mul_eq_one_right hab
  refine ⟨a,ha.symm,?_⟩
  simpa only [hb',Units.smul_def] using hb.symm

theorem model_opposite_pair_scalar_reduction {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (g : Model F m)
    (he : g • firstSpecialPoint (F := F) m = firstSpecialPoint m)
    (hf : g • oppositeSpecialPoint (F := F) m = oppositeSpecialPoint m) :
    ∃ s : Fˣ,
      ((modelSuzukiScalarHom hcard s)⁻¹*g).val (rootVector (0,0)) = rootVector (0,0) ∧
      ((modelSuzukiScalarHom hcard s)⁻¹*g).val (rootVector (0,7)) = rootVector (0,7) := by
  obtain ⟨a,ha,hb⟩ := model_opposite_pair_scalars g he hf
  let s : Fˣ := Units.map (thetaInv F m).toMonoidHom a
  have hs : thetaUnits m s=a := by
    apply Units.ext
    exact theta_thetaInv hcard (a : F)
  have hse : (modelSuzukiScalarHom hcard s).val (rootVector (0,0)) =
      (a : F) • rootVector (0,0) := by
    have hh := modelSuzukiProduct_first_root hcard 1 s
    change ((modelSuzukiEmbedding m hcard 1)*(modelSuzukiScalarHom hcard s)).val
      (rootVector (0,0)) = _ at hh
    simpa only [map_one,one_mul,hs] using hh
  have hsf : (modelSuzukiScalarHom hcard s).val (rootVector (0,7)) =
      ((a⁻¹ : Fˣ) : F) • rootVector (0,7) := by
    have hh := modelSuzukiProduct_opposite_root hcard 1 s
    change ((modelSuzukiEmbedding m hcard 1)*(modelSuzukiScalarHom hcard s)).val
      (rootVector (0,7)) = _ at hh
    simpa only [map_one,one_mul,hs] using hh
  refine ⟨s,?_,?_⟩
  · change (modelSuzukiScalarHom hcard s).val.symm (g.val (rootVector (0,0))) = _
    rw [ha,← hse,LinearEquiv.symm_apply_apply]
  · change (modelSuzukiScalarHom hcard s).val.symm (g.val (rootVector (0,7))) = _
    rw [hb,← hsf,LinearEquiv.symm_apply_apply]

end Atlas.ReeF4

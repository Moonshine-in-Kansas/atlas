import Atlas.LinearGroups.Chevalley.Comparison.TypeASpecialLinearEquiv
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionCenterQuotient

/-! The actual new adjoint type-A group and the existing PSL matrix quotient
are linked through the literal defining-weight representation and both full
centers. The comparison is marked on positive and negative simple roots. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeA

def projectiveEquiv (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K] [Finite K] :
    Model (.A r hr) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) K :=
  (selectedWeightCompanionCenterQuotientAdjointEquiv (.A r hr) K).symm.trans
    (QuotientGroup.congr _ _ (specialLinearEquiv r hr K)
      (Subgroup.map_center_eq (specialLinearEquiv r hr K)))

theorem projectiveEquiv_rho (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K] [Finite K]
    (g : SelectedWeightCompanion (.A r hr) K) :
    projectiveEquiv r hr K (selectedWeightCompanionRho (.A r hr) K g) =
      QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) K))
        (specialLinearEquiv r hr K g) := by
  let e := selectedWeightCompanionCenterQuotientAdjointEquiv (.A r hr) K
  have he : e (QuotientGroup.mk'
      (Subgroup.center (SelectedWeightCompanion (.A r hr) K)) g) =
      selectedWeightCompanionRho (.A r hr) K g :=
    weightCompanionCenterQuotientAdjointEquiv_mk
      (rootDatum (.A r hr)).pairing (rootDatum (.A r hr)).base
      (selectedWeightOrbits (.A r hr)) (selectedWeightOrbits_closed (.A r hr))
      (selectedWeightOrbits_minuscule (.A r hr)) K
      (rootDatum_simpleDiamondProducts (.A r hr)) g
  change QuotientGroup.congr _ _ (specialLinearEquiv r hr K)
      (Subgroup.map_center_eq (specialLinearEquiv r hr K))
      (e.symm (selectedWeightCompanionRho (.A r hr) K g)) = _
  rw [← he, e.symm_apply_apply]
  rfl

theorem projectiveEquiv_X (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K] [Finite K]
    (i : Fin r) (t : K) :
    projectiveEquiv r hr K (modelX (.A r hr) K i t) =
      QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) K))
        (Matrix.SpecialLinearGroup.transvection (adjacent_ne i) t) := by
  change projectiveEquiv r hr K (selectedWeightCompanionRho (.A r hr) K
    (selectedWeightCompanionX (.A r hr) K i t)) = _
  rw [projectiveEquiv_rho r hr K, specialLinearEquiv_X r hr K i t]

theorem projectiveEquiv_Y (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K] [Finite K]
    (i : Fin r) (t : K) :
    projectiveEquiv r hr K (modelY (.A r hr) K i t) =
      QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) K))
        (Matrix.SpecialLinearGroup.transvection (adjacent_ne i).symm t) := by
  change projectiveEquiv r hr K (selectedWeightCompanionRho (.A r hr) K
    (selectedWeightCompanionY (.A r hr) K i t)) = _
  rw [projectiveEquiv_rho r hr K, specialLinearEquiv_Y r hr K i t]

end Atlas.Chevalley.Comparison.TypeA

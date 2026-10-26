import Atlas.LinearGroups.Chevalley.Comparison.TypeCSymplecticEquiv
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionCenterQuotient

/-! The actual adjoint type-C model is identified with the existing PSp by
transporting the concrete symplectic isomorphism through the full centers.
Both signs of every simple root retain their literal matrix markings. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeC

private theorem adjacent_ne {n : ℕ} (i : Fin n) : i.castSucc ≠ i.succ := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_succ] at hv
  omega

def projectiveEquiv (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K] [Finite K] :
    Model (.C (n + 1) hn) K ≃* Atlas.Symplectic.PSp (n + 1) K :=
  (selectedWeightCompanionCenterQuotientAdjointEquiv (.C (n + 1) hn) K).symm.trans
    (QuotientGroup.congr _ _ (symplecticEquiv n hn K)
      (Subgroup.map_center_eq (symplecticEquiv n hn K)))

theorem projectiveEquiv_rho (n : ℕ) (hn : 2 ≤ n + 1)
    (K : Type*) [Field K] [Finite K]
    (g : SelectedWeightCompanion (.C (n + 1) hn) K) :
    projectiveEquiv n hn K (selectedWeightCompanionRho (.C (n + 1) hn) K g) =
      Atlas.Symplectic.projection (symplecticEquiv n hn K g) := by
  let e := selectedWeightCompanionCenterQuotientAdjointEquiv (.C (n + 1) hn) K
  have he : e (QuotientGroup.mk'
      (Subgroup.center (SelectedWeightCompanion (.C (n + 1) hn) K)) g) =
      selectedWeightCompanionRho (.C (n + 1) hn) K g :=
    weightCompanionCenterQuotientAdjointEquiv_mk
      (rootDatum (.C (n + 1) hn)).pairing (rootDatum (.C (n + 1) hn)).base
      (selectedWeightOrbits (.C (n + 1) hn))
      (selectedWeightOrbits_closed (.C (n + 1) hn))
      (selectedWeightOrbits_minuscule (.C (n + 1) hn)) K
      (rootDatum_simpleDiamondProducts (.C (n + 1) hn)) g
  change QuotientGroup.congr _ _ (symplecticEquiv n hn K)
      (Subgroup.map_center_eq (symplecticEquiv n hn K))
      (e.symm (selectedWeightCompanionRho (.C (n + 1) hn) K g)) = _
  rw [← he, e.symm_apply_apply]
  rfl

theorem projectiveEquiv_X_short (n : ℕ) (hn : 2 ≤ n + 1)
    (K : Type*) [Field K] [Finite K] (i : Fin n) (t : K) :
    projectiveEquiv n hn K (modelX (.C (n + 1) hn) K i.castSucc t) =
      Atlas.Symplectic.projection
        ⟨shortMatrix (n + 1) K i.castSucc i.succ t,
          shortMatrix_mem (n + 1) K i.castSucc i.succ (adjacent_ne i) t⟩ := by
  change projectiveEquiv n hn K (selectedWeightCompanionRho (.C (n + 1) hn) K
    (selectedWeightCompanionX (.C (n + 1) hn) K i.castSucc t)) = _
  rw [projectiveEquiv_rho n hn K, symplecticEquiv_X_short n hn K i t]

theorem projectiveEquiv_Y_short (n : ℕ) (hn : 2 ≤ n + 1)
    (K : Type*) [Field K] [Finite K] (i : Fin n) (t : K) :
    projectiveEquiv n hn K (modelY (.C (n + 1) hn) K i.castSucc t) =
      Atlas.Symplectic.projection
        ⟨shortMatrix (n + 1) K i.succ i.castSucc t,
          shortMatrix_mem (n + 1) K i.succ i.castSucc (Ne.symm (adjacent_ne i)) t⟩ := by
  change projectiveEquiv n hn K (selectedWeightCompanionRho (.C (n + 1) hn) K
    (selectedWeightCompanionY (.C (n + 1) hn) K i.castSucc t)) = _
  rw [projectiveEquiv_rho n hn K, symplecticEquiv_Y_short n hn K i t]

theorem projectiveEquiv_X_long (n : ℕ) (hn : 2 ≤ n + 1)
    (K : Type*) [Field K] [Finite K] (t : K) :
    projectiveEquiv n hn K (modelX (.C (n + 1) hn) K (Fin.last n) t) =
      Atlas.Symplectic.projection
        ⟨longMatrix (n + 1) K (Fin.last n) t,
          longMatrix_mem (n + 1) K (Fin.last n) t⟩ := by
  change projectiveEquiv n hn K (selectedWeightCompanionRho (.C (n + 1) hn) K
    (selectedWeightCompanionX (.C (n + 1) hn) K (Fin.last n) t)) = _
  rw [projectiveEquiv_rho n hn K, symplecticEquiv_X_long n hn K t]

theorem projectiveEquiv_Y_long (n : ℕ) (hn : 2 ≤ n + 1)
    (K : Type*) [Field K] [Finite K] (t : K) :
    projectiveEquiv n hn K (modelY (.C (n + 1) hn) K (Fin.last n) t) =
      Atlas.Symplectic.projection
        ⟨(longMatrix (n + 1) K (Fin.last n) t).transpose,
          longMatrix_transpose_mem (n + 1) K (Fin.last n) t⟩ := by
  change projectiveEquiv n hn K (selectedWeightCompanionRho (.C (n + 1) hn) K
    (selectedWeightCompanionY (.C (n + 1) hn) K (Fin.last n) t)) = _
  rw [projectiveEquiv_rho n hn K, symplecticEquiv_Y_long n hn K t]

end Atlas.Chevalley.Comparison.TypeC

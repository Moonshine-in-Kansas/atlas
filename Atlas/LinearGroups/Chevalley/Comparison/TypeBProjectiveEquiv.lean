import Atlas.LinearGroups.Chevalley.Comparison.TypeBOrthogonalKernel

/-! The actual adjoint B model and the original projective elementary odd
quadratic group are isomorphic through the constructed spin-vector map.
All finite fields, including B2(F2), retain the literal root markings. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeB
open Atlas.Orthogonal
variable (n : ℕ) (hn : 2 ≤ n+1) (K : Type*) [Field K] [Finite K]

/-- First quotient by the proved full center, then the actual surjection. -/
def modelElementaryEquiv : Model (.B (n+1) hn) K ≃*
    elementarySubgroup (formB (n+1) K) :=
  (selectedWeightCompanionCenterQuotientAdjointEquiv (.B (n+1) hn) K).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (elementaryHom_ker_eq_center n hn K).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (elementaryHom n hn K)
        (elementaryHom_surjective n hn K)))

theorem modelElementaryEquiv_rho (g : SelectedWeightCompanion (.B (n+1) hn) K) :
    modelElementaryEquiv n hn K (selectedWeightCompanionRho (.B (n+1) hn) K g) =
      elementaryHom n hn K g := by
  let e := selectedWeightCompanionCenterQuotientAdjointEquiv (.B (n+1) hn) K
  have he : e (QuotientGroup.mk' (Subgroup.center
      (SelectedWeightCompanion (.B (n+1) hn) K)) g) =
      selectedWeightCompanionRho (.B (n+1) hn) K g :=
    weightCompanionCenterQuotientAdjointEquiv_mk
      (rootDatum (.B (n+1) hn)).pairing (rootDatum (.B (n+1) hn)).base
      (selectedWeightOrbits (.B (n+1) hn))
      (selectedWeightOrbits_closed (.B (n+1) hn))
      (selectedWeightOrbits_minuscule (.B (n+1) hn)) K
      (rootDatum_simpleDiamondProducts (.B (n+1) hn)) g
  change ((QuotientGroup.quotientMulEquivOfEq
      (elementaryHom_ker_eq_center n hn K).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (elementaryHom n hn K)
        (elementaryHom_surjective n hn K)))
      (e.symm (selectedWeightCompanionRho (.B (n+1) hn) K g)) = _
  rw [← he, e.symm_apply_apply]
  rfl

/-- The target is the existing scalar quotient, not an order-based recognition. -/
def projectiveEquiv : Model (.B (n+1) hn) K ≃* B (n+1) K :=
  (modelElementaryEquiv n hn K).trans (B_elementaryEquiv (F := K) (n+1) hn).symm

theorem projectiveEquiv_rho (g : SelectedWeightCompanion (.B (n+1) hn) K) :
    projectiveEquiv n hn K (selectedWeightCompanionRho (.B (n+1) hn) K g) =
      projectiveElementaryMap (formB (n+1) K) (elementaryHom n hn K g) := by
  apply (B_elementaryEquiv (F := K) (n+1) hn).injective
  change (B_elementaryEquiv (F := K) (n+1) hn)
    ((B_elementaryEquiv (F := K) (n+1) hn).symm
      (modelElementaryEquiv n hn K (selectedWeightCompanionRho (.B (n+1) hn) K g))) = _
  rw [MulEquiv.apply_symm_apply, modelElementaryEquiv_rho]
  rfl

theorem projectiveEquiv_X_long (i : Fin n) (t : K) :
    projectiveEquiv n hn K (modelX (.B (n+1) hn) K i.castSucc t) =
      projectiveElementaryMap (formB (n+1) K)
        ⟨oddLong (n+1) K i.castSucc i.succ (ne_of_lt i.castSucc_lt_succ) t,
          oddLong_mem_elementary _ _ _ _ _ _⟩ := by
  change projectiveEquiv n hn K (selectedWeightCompanionRho (.B (n+1) hn) K
    (selectedWeightCompanionX (.B (n+1) hn) K i.castSucc t)) = _
  rw [projectiveEquiv_rho]
  congr 1
  exact Subtype.ext (orthogonalHom_X_long n hn K i t)

theorem projectiveEquiv_Y_long (i : Fin n) (t : K) :
    projectiveEquiv n hn K (modelY (.B (n+1) hn) K i.castSucc t) =
      projectiveElementaryMap (formB (n+1) K)
        ⟨oddLong (n+1) K i.succ i.castSucc (Ne.symm (ne_of_lt i.castSucc_lt_succ)) t,
          oddLong_mem_elementary _ _ _ _ _ _⟩ := by
  change projectiveEquiv n hn K (selectedWeightCompanionRho (.B (n+1) hn) K
    (selectedWeightCompanionY (.B (n+1) hn) K i.castSucc t)) = _
  rw [projectiveEquiv_rho]
  congr 1
  exact Subtype.ext (orthogonalHom_Y_long n hn K i t)

theorem projectiveEquiv_X_short (t : K) :
    projectiveEquiv n hn K (modelX (.B (n+1) hn) K (Fin.last n) t) =
      projectiveElementaryMap (formB (n+1) K)
        ⟨oddShortUpper (n+1) K (Fin.last n) t, oddShortUpper_mem_elementary _ _ _ _⟩ := by
  change projectiveEquiv n hn K (selectedWeightCompanionRho (.B (n+1) hn) K
    (selectedWeightCompanionX (.B (n+1) hn) K (Fin.last n) t)) = _
  rw [projectiveEquiv_rho]
  congr 1
  exact Subtype.ext (orthogonalHom_X_short n hn K t)

theorem projectiveEquiv_Y_short (t : K) :
    projectiveEquiv n hn K (modelY (.B (n+1) hn) K (Fin.last n) t) =
      projectiveElementaryMap (formB (n+1) K)
        ⟨oddShortLower (n+1) K (Fin.last n) t, oddShortLower_mem_elementary _ _ _ _⟩ := by
  change projectiveEquiv n hn K (selectedWeightCompanionRho (.B (n+1) hn) K
    (selectedWeightCompanionY (.B (n+1) hn) K (Fin.last n) t)) = _
  rw [projectiveEquiv_rho]
  congr 1
  exact Subtype.ext (orthogonalHom_Y_short n hn K t)

end Atlas.Chevalley.Comparison.TypeB

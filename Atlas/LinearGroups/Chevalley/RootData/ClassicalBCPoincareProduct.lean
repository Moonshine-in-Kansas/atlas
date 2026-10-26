import Atlas.LinearGroups.Chevalley.RootData.ClassicalBParabolicRepresentatives
import Atlas.LinearGroups.Chevalley.RootData.ClassicalBLowerRankParabolic
import Atlas.LinearGroups.Chevalley.RootData.ClassicalBCWeylDuality
import Atlas.LinearGroups.Chevalley.RootData.ParabolicPoincareFactor

/-! The uniform B/C degree product is obtained from literal signed-axis
minimal representatives and the actual lower-rank parabolic equivalence. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalBParabolic
open Classical ClassicalData RootData

theorem rootWeylPoincareEval_B_succ (n q : ℕ) :
    rootWeylPoincareEval (pairingB (n + 2)) (baseB (n + 1)) q =
      rootWeylPoincareEval (pairingB (n + 1)) (baseB n) q *
        (∑ k : Fin (2 * (n + 2)), q ^ k.val) := by
  letI : Fintype (W n) := Fintype.ofFinite _
  letI : Fintype (rootParabolicRepresentatives (pairingB (n + 2)) (baseB (n + 1))
      (J (n + 1))) := by
    unfold rootParabolicRepresentatives
    exact Fintype.ofFinite _
  letI : Fintype (rootParabolicSubgroup (pairingB (n + 2)) (baseB (n + 1))
      (J (n + 1))) := Fintype.ofFinite _
  rw [rootWeylPoincareEval_parabolic_factor (pairingB (n + 2)) (baseB (n + 1)) (J (n + 1))]
  rw [← (pathRepresentativeEquiv (n + 1)).sum_comp
    (fun x => q ^ rootWeylLength (pairingB (n + 2)) (baseB (n + 1)) x.val)]
  rw [← (lowerRankParabolicEquiv n).toEquiv.sum_comp
    (fun x => q ^ rootWeylLength (pairingB (n + 2)) (baseB (n + 1)) x.val)]
  simp only [pathRepresentativeEquiv_length]
  have hsum :
      (∑ w : W n, q ^ rootWeylLength (pairingB (n + 2)) (baseB (n + 1))
        ((lowerRankParabolicEquiv n).toEquiv w).val) =
          rootWeylPoincareEval (pairingB (n + 1)) (baseB n) q := by
    change (∑ w : W n, q ^ rootWeylLength (pairingB (n + 2)) (baseB (n + 1))
      ((lowerRankParabolicEquiv n).toEquiv w).val) =
        ∑ w : W n, q ^ rootWeylLength (pairingB (n + 1)) (baseB n) w
    apply Finset.sum_congr rfl
    intro w hw
    change q ^ rootWeylLength (pairingB (n + 2)) (baseB (n + 1))
      (lowerRankParabolicEquiv n w).val = _
    exact congrArg (fun k : ℕ => q ^ k) (lowerRankParabolicEquiv_length n w)
  rw [hsum]
  exact mul_comm _ _

private theorem J_zero : J 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨k, rfl⟩ := (baseBIndexEquiv 0).surjective i
  have hk : k = 0 := by
    apply Fin.ext
    have hklt := k.isLt
    change k.val = 0
    omega
  subst k
  exact (Finset.mem_erase.mp hi).1 rfl

private theorem rankOne_parabolic_eq_one
    (v : rootParabolicSubgroup (pairingB 1) (baseB 0) (J 0)) : v.val = 1 := by
  have hbot : rootParabolicSubgroup (pairingB 1) (baseB 0) (J 0) = ⊥ := by
    simp [rootParabolicSubgroup, J_zero]
  exact Subgroup.mem_bot.mp (hbot ▸ v.property)

/-- The rank-one base is computed from its actual two minimal cosets. -/
theorem rootWeylPoincareEval_B_one (q : ℕ) :
    rootWeylPoincareEval (pairingB 1) (baseB 0) q = ∑ k : Fin 2, q ^ k.val := by
  letI : Fintype (rootParabolicRepresentatives (pairingB 1) (baseB 0) (J 0)) := by
    unfold rootParabolicRepresentatives
    exact Fintype.ofFinite _
  letI : Unique (rootParabolicSubgroup (pairingB 1) (baseB 0) (J 0)) := {
    default := 1
    uniq := fun v => Subtype.ext (rankOne_parabolic_eq_one v) }
  rw [rootWeylPoincareEval_parabolic_factor (pairingB 1) (baseB 0) (J 0)]
  rw [← (pathRepresentativeEquiv 0).sum_comp
    (fun x => q ^ rootWeylLength (pairingB 1) (baseB 0) x.val)]
  simp only [pathRepresentativeEquiv_length, rankOne_parabolic_eq_one,
    rootWeylLength_one, pow_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_unique, one_smul, mul_one]

/-- Exact Poincaré product for every positive rank of the actual B root pairing. -/
theorem rootWeylPoincareEval_B_product (n q : ℕ) :
    rootWeylPoincareEval (pairingB (n + 1)) (baseB n) q =
      ∏ d ∈ Finset.range (n + 1), (∑ k : Fin (2 * (d + 1)), q ^ k.val) := by
  induction n with
  | zero => simpa using rootWeylPoincareEval_B_one q
  | succ n ih =>
    rw [rootWeylPoincareEval_B_succ, Finset.prod_range_succ, ih]

/-- Type C has the same actual root-label Weyl image and shortest lengths;
no isomorphism of the constructed B/C linear groups is asserted. -/
theorem rootWeylPoincareEval_C_product (n q : ℕ) :
    rootWeylPoincareEval (pairingC (n + 1)) (baseC n) q =
      ∏ d ∈ Finset.range (n + 1), (∑ k : Fin (2 * (d + 1)), q ^ k.val) := by
  rw [← rootWeylPoincareEval_B_eq_C, rootWeylPoincareEval_B_product]

end Atlas.Chevalley.ClassicalBParabolic

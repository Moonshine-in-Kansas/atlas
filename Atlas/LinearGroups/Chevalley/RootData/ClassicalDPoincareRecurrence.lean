import Atlas.LinearGroups.Chevalley.RootData.ClassicalDParabolicRepresentatives
import Atlas.LinearGroups.Chevalley.RootData.ClassicalDLowerRankParabolic
import Atlas.LinearGroups.Chevalley.RootData.ParabolicPoincareFactor
import Mathlib.Data.Fin.Rev

/-! The actual type-D parabolic recurrence. The quotient factor has the
repeated middle coefficient dictated by its two distinct signed fork labels.
The D₂ base and the final degree product are separate subsequent statements. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalDParabolic
open Classical ClassicalData RootData

/-- Exact distance histogram on the 2r signed coordinates, including rank two. -/
theorem signedCoordinate_distance_sum (n q : ℕ) :
    (∑ c : Fin (n + 2) × Bool, q ^ ClassicalDAxis.distance n c) =
      (∑ k : Fin (n + 2), q ^ k.val) * (1 + q ^ (n + 1)) := by
  have hnegative : (∑ k : Fin (n + 2), q ^ (2 * (n + 1) - k.val)) =
      q ^ (n + 1) * ∑ k : Fin (n + 2), q ^ k.val := by
    calc
      _ = ∑ k : Fin (n + 2), q ^ (n + 1) * q ^ k.rev.val := by
        apply Finset.sum_congr rfl
        intro k hk
        have he : 2 * (n + 1) - k.val = n + 1 + k.rev.val := by
          rw [Fin.val_rev]
          have h := k.isLt
          omega
        rw [he, pow_add]
      _ = q ^ (n + 1) * ∑ k : Fin (n + 2), q ^ k.rev.val := by
        rw [Finset.mul_sum]
      _ = _ := by
        congr 1
        simpa only [Fin.revPerm_apply] using
          Equiv.sum_comp (Fin.revPerm (n := n + 2)) (fun k : Fin (n + 2) => q ^ k.val)
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, ClassicalDAxis.distance, Bool.true_eq,
    Bool.false_eq_true, ↓reduceIte]
  rw [Finset.sum_add_distrib, hnegative]
  ring

/-- A genuine recurrence for the length sum of the actual D Weyl image.
The smaller factor is identified by the actual integral tail action. -/
theorem rootWeylPoincareEval_D_succ (n q : ℕ) :
    rootWeylPoincareEval (pairingD (n + 3)) (baseD (n + 1)) q =
      rootWeylPoincareEval (pairingD (n + 2)) (baseD n) q *
        ((∑ k : Fin (n + 3), q ^ k.val) * (1 + q ^ (n + 2))) := by
  letI : Fintype (ClassicalDTail.W n) := Fintype.ofFinite _
  letI : Fintype (rootParabolicRepresentatives (pairingD (n + 3)) (baseD (n + 1))
      (J n)) := by
    unfold rootParabolicRepresentatives
    exact Fintype.ofFinite _
  letI : Fintype (rootParabolicSubgroup (pairingD (n + 3)) (baseD (n + 1))
      (J n)) := Fintype.ofFinite _
  have hreps :
      (∑ x : rootParabolicRepresentatives (pairingD (n + 3)) (baseD (n + 1))
        (J n), q ^ rootWeylLength (pairingD (n + 3)) (baseD (n + 1)) x.val) =
          (∑ k : Fin (n + 3), q ^ k.val) * (1 + q ^ (n + 2)) := by
    calc
      _ = ∑ c : Fin (n + 3) × Bool,
          q ^ rootWeylLength (pairingD (n + 3)) (baseD (n + 1))
            (coordinateRepresentativeEquiv n c).val :=
        ((coordinateRepresentativeEquiv n).sum_comp
          (fun x => q ^ rootWeylLength (pairingD (n + 3)) (baseD (n + 1)) x.val)).symm
      _ = ∑ c : Fin (n + 3) × Bool, q ^ ClassicalDAxis.distance (n + 1) c := by
        apply Finset.sum_congr rfl
        intro c hc
        exact congrArg (fun k : ℕ => q ^ k) (coordinateRepresentativeEquiv_length n c)
      _ = _ := signedCoordinate_distance_sum (n + 1) q
  have hparabolic :
      (∑ x : rootParabolicSubgroup (pairingD (n + 3)) (baseD (n + 1))
        (J n), q ^ rootWeylLength (pairingD (n + 3)) (baseD (n + 1)) x.val) =
          rootWeylPoincareEval (pairingD (n + 2)) (baseD n) q := by
    calc
      _ = ∑ w : ClassicalDTail.W n,
          q ^ rootWeylLength (pairingD (n + 3)) (baseD (n + 1))
            ((ClassicalDTail.lowerRankParabolicEquiv n).toEquiv w).val :=
        ((ClassicalDTail.lowerRankParabolicEquiv n).toEquiv.sum_comp
          (fun x => q ^ rootWeylLength (pairingD (n + 3)) (baseD (n + 1)) x.val)).symm
      _ = ∑ w : ClassicalDTail.W n,
          q ^ rootWeylLength (pairingD (n + 2)) (baseD n) w := by
        apply Finset.sum_congr rfl
        intro w hw
        change q ^ rootWeylLength (pairingD (n + 3)) (baseD (n + 1))
          (ClassicalDTail.lowerRankParabolicEquiv n w).val = _
        exact congrArg (fun k : ℕ => q ^ k) (ClassicalDTail.lowerRankParabolicEquiv_length n w)
      _ = _ := rfl
  rw [rootWeylPoincareEval_parabolic_factor (pairingD (n + 3)) (baseD (n + 1))
    (J n), hreps, hparabolic]
  exact mul_comm _ _

end Atlas.Chevalley.ClassicalDParabolic

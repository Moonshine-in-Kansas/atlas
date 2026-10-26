import Atlas.LinearGroups.Chevalley.RootData.TypeALowerRankParabolic
import Atlas.LinearGroups.Chevalley.RootData.ParabolicPoincareFactor

/-! A uniform recurrence and product for the Poincare sum of the actual type-A
Weyl image. The product follows by induction from actual parabolic cosets. -/
noncomputable section
namespace Atlas.Chevalley.TypeAData
open Classical RootData

theorem rootWeylPoincareEval_A_succ (r q : ℕ) :
    rootWeylPoincareEval (pairing (r + 2)) (base (r + 1)) q =
      rootWeylPoincareEval (pairing (r + 1)) (base r) q *
        (∑ k : Fin (r + 2), q ^ k.val) := by
  let : Fintype (pairing (r + 1)).weylGroupToPerm.range := Fintype.ofFinite _
  let : Fintype (rootParabolicRepresentatives (pairing (r + 2)) (base (r + 1))
      (firstZeroWalls r)) := by
    unfold rootParabolicRepresentatives
    exact Fintype.ofFinite _
  let : Fintype (rootParabolicSubgroup (pairing (r + 2)) (base (r + 1))
      (firstZeroWalls r)) := Fintype.ofFinite _
  have hreps :
      (∑ x : rootParabolicRepresentatives (pairing (r + 2)) (base (r + 1))
        (firstZeroWalls r), q ^ rootWeylLength (pairing (r + 2)) (base (r + 1)) x.val) =
          ∑ k : Fin (r + 2), q ^ k.val := by
    calc
      _ = ∑ k : Fin (r + 2),
          q ^ rootWeylLength (pairing (r + 2)) (base (r + 1))
            (coordinateRepresentativeEquiv r k).val :=
        ((coordinateRepresentativeEquiv r).sum_comp
          (fun x => q ^ rootWeylLength (pairing (r + 2)) (base (r + 1)) x.val)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        exact congrArg (fun n : ℕ => q ^ n) (coordinateRepresentativeEquiv_length r k)
  have hparabolic :
      (∑ x : rootParabolicSubgroup (pairing (r + 2)) (base (r + 1))
        (firstZeroWalls r), q ^ rootWeylLength (pairing (r + 2)) (base (r + 1)) x.val) =
          rootWeylPoincareEval (pairing (r + 1)) (base r) q := by
    calc
      _ = ∑ w : (pairing (r + 1)).weylGroupToPerm.range,
          q ^ rootWeylLength (pairing (r + 2)) (base (r + 1))
            ((lowerRankParabolicEquiv r).toEquiv w).val :=
        ((lowerRankParabolicEquiv r).toEquiv.sum_comp
          (fun x => q ^ rootWeylLength (pairing (r + 2)) (base (r + 1)) x.val)).symm
      _ = ∑ w : (pairing (r + 1)).weylGroupToPerm.range,
          q ^ rootWeylLength (pairing (r + 1)) (base r) w := by
        apply Finset.sum_congr rfl
        intro w hw
        change q ^ rootWeylLength (pairing (r + 2)) (base (r + 1))
          (lowerRankParabolicEquiv r w).val = _
        exact congrArg (fun n : ℕ => q ^ n) (lowerRankParabolicEquiv_length r w)
      _ = _ := rfl
  rw [rootWeylPoincareEval_parabolic_factor (pairing (r + 2)) (base (r + 1))
    (firstZeroWalls r), hreps, hparabolic]
  exact mul_comm _ _

theorem rootWeylPoincareEval_A_zero (q : ℕ) :
    rootWeylPoincareEval (pairing 1) (base 0) q = 1 := by
  let : Fintype (pairing 1).weylGroupToPerm.range := Fintype.ofFinite _
  have hone (w : (pairing 1).weylGroupToPerm.range) : w = 1 := by
    apply (coordinateWeylEquiv 1).symm.injective
    exact Subsingleton.elim _ _
  change (∑ w : (pairing 1).weylGroupToPerm.range,
    q ^ rootWeylLength (pairing 1) (base 0) w) = 1
  calc
    _ = q ^ rootWeylLength (pairing 1) (base 0) 1 := by
      apply Finset.sum_eq_single 1
      · intro w hw hne
        exact (hne (hone w)).elim
      · intro h
        exact (h (Finset.mem_univ _)).elim
    _ = 1 := by rw [rootWeylLength_one, pow_zero]

/-- The actual type-A Weyl sum has factors [2]q,[3]q,...,[r+1]q in every rank. -/
theorem rootWeylPoincareEval_A_product (r q : ℕ) :
    rootWeylPoincareEval (pairing (r + 1)) (base r) q =
      ∏ d ∈ Finset.range r, (∑ k : Fin (d + 2), q ^ k.val) := by
  induction r with
  | zero => simp [rootWeylPoincareEval_A_zero]
  | succ r ih =>
    rw [rootWeylPoincareEval_A_succ, Finset.prod_range_succ, ih]

end Atlas.Chevalley.TypeAData

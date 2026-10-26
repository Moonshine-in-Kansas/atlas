import Atlas.LinearGroups.Chevalley.Integral.TorusAction
import Atlas.LinearGroups.Chevalley.TorusBlock

noncomputable section
open scoped Matrix
namespace Atlas.Chevalley.Integral
variable {R : Type*} [CommRing R]

theorem unit_zpow_sub_nat_val (t : Rˣ) (a c : ℕ) :
    ((t ^ ((a : ℤ) - (c : ℤ))).val : R) = t.val^a * t.inv^c := by
  rw [zpow_sub, zpow_natCast, zpow_natCast]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  rfl

end Atlas.Chevalley.Integral
namespace Atlas.Chevalley
open Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

/-- Weight of each actual Geck coordinate, not an abstract weight-space assumption. -/
def adjointTorusCoordinate (i : b.support) (t : Rˣ) : b.support ⊕ ι → R
  | .inl _ => 1
  | .inr j => (t ^ P.pairingIn ℤ j i).val

theorem adjointTorus_root_independent (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (t : Rˣ) :
    (adjointTorus P b R i t).val.val *ᵥ rootVector P b R j =
      (t ^ P.pairingIn ℤ j i).val • rootVector P b R j := by
  let k : Fin (geckStringLength P i j+1) := ⟨P.chainBotCoeff i j,
    Nat.lt_succ_of_le (geckString_original_le P i j h)⟩
  have hk : geckStringIndex P i j h k = j := geckStringIndex_original P i j h
  have hw := geckString_weight P b i j h k
  rw [hk] at hw
  have hc := congrArg (fun A => fun row => A row k)
    (geckStringMatrixOver_torus P b R i j h t)
  simp only [stringTorus, Matrix.mul_diagonal] at hc
  change (adjointTorus P b R i t).val.val *ᵥ
    (fun row => geckStringMatrixOver P b R i j h row k) = _ at hc
  have hv : (fun row => geckStringMatrixOver P b R i j h row k) =
      rootVector P b R j := by
    ext row
    simp only [geckStringMatrixOver, Matrix.map_apply, geckStringMatrix_entry, hk]
    rfl
  rw [hv] at hc
  rw [← hw, unit_zpow_sub_nat_val]
  ext row
  simpa only [← hv, Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun hc row

/-- Covers every root, including both opposite simple-root columns. -/
theorem adjointTorus_root (i : b.support) (j : ι) (t : Rˣ) :
    (adjointTorus P b R i t).val.val *ᵥ rootVector P b R j =
      (t ^ P.pairingIn ℤ j i).val • rootVector P b R j := by
  by_cases h : LinearIndependent ℤ ![P.root i, P.root j]
  · exact adjointTorus_root_independent P b R i j h t
  · rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) i j h with hp | hn
    · have hj : j = i := (P.root.injective hp).symm
      subst j
      simpa using adjointTorus_positive P b R i t
    · have hj : j = P.reflectionPerm i i := by
        apply P.root_eq_neg_iff.mp
        simpa only [neg_neg] using congrArg Neg.neg hn.symm
      subst j
      simpa [P.pairingIn_reflectionPerm_self_left] using adjointTorus_negative P b R i t

theorem adjointTorus_matrix (i : b.support) (t : Rˣ) :
    (adjointTorus P b R i t).val.val =
      Matrix.diagonal (adjointTorusCoordinate P b R i t) := by
  have hv (j : ι) : rootVector P b R j = Pi.single (Sum.inr j) 1 := by
    ext row
    by_cases h : row = Sum.inr j <;>
      simp [rootVector, RootPairing.GeckConstruction.v, Function.comp_def, Pi.single_apply, h]
  have hu (j : b.support) : cartanVector P b R j = Pi.single (Sum.inl j) 1 := by
    ext row
    by_cases h : row = Sum.inl j <;>
      simp [cartanVector, RootPairing.GeckConstruction.u, Function.comp_def, Pi.single_apply, h]
  ext row col
  cases col with
  | inl j =>
    have hc := congrFun (adjointTorus_cartan P b R i j t) row
    rw [hu, Matrix.mulVec_single_one] at hc
    by_cases h : row = Sum.inl j
    · subst row
      simpa [Matrix.diagonal, adjointTorusCoordinate] using hc
    · simpa [Matrix.diagonal, adjointTorusCoordinate, Pi.single_apply, h, Ne.symm h] using hc
  | inr j =>
    have hc := congrFun (adjointTorus_root P b R i j t) row
    rw [hv, Matrix.mulVec_single_one] at hc
    by_cases h : row = Sum.inr j
    · subst row
      simpa [Matrix.diagonal, adjointTorusCoordinate] using hc
    · simpa [Matrix.diagonal, adjointTorusCoordinate, Pi.single_apply, h, Ne.symm h] using hc

end Atlas.Chevalley

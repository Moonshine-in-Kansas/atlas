import Atlas.LinearGroups.Chevalley.Integral.RootStringWeyl
import Atlas.LinearGroups.Chevalley.Integral.RootStringReflection
import Atlas.LinearGroups.Chevalley.Integral.StringWeyl

/-! Actual Weyl action on ordinary root coordinates, including the root-string
sign. These formulas are uniform in the coefficient ring. -/
noncomputable section
open scoped Matrix
namespace Atlas.Chevalley.Integral
variable {R : Type*} [CommRing R]

theorem matrix_mul_stringWeyl_entry {d : Type*} (n : ℕ) (hn : n ≤ 3)
    (C : Matrix d (Fin (n+1)) R) (t : Rˣ) (row : d) (k : Fin (n+1)) :
    (C * stringWeyl n t) row k =
      C row k.rev * ((-1:R)^k.val * t.val^(n-k.val) * t.inv^k.val) := by
  simp only [Matrix.mul_apply, stringWeyl_entry n hn t, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Atlas.Chevalley.Integral
namespace Atlas.Chevalley
open Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

/-- For β independent of αᵢ, the actual group Weyl word takes its literal root
coordinate to the reflected coordinate with the explicit integral-string sign. -/
theorem adjointWeyl_root_independent (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (t : Rˣ) :
    (adjointWeyl P b R i t).val.val *ᵥ rootVector P b R j =
      ((-1:R)^(P.chainBotCoeff i j) * t.val^(P.chainTopCoeff i j) *
        t.inv^(P.chainBotCoeff i j)) • rootVector P b R (P.reflectionPerm i j) := by
  let k : Fin (geckStringLength P i j+1) := ⟨P.chainBotCoeff i j,
    Nat.lt_succ_of_le (geckString_original_le P i j h)⟩
  have hk : geckStringIndex P i j h k = j := geckStringIndex_original P i j h
  have hn : geckStringLength P i j-k.val = P.chainTopCoeff i j := by
    dsimp only [k]
    rw [geckStringLength_eq P b i j h]
    omega
  have hm := geckStringMatrixOver_weyl P b R i j h t
  change (adjointWeyl P b R i t).val.val * geckStringMatrixOver P b R i j h =
    geckStringMatrixOver P b R i j h * stringWeyl (geckStringLength P i j) t at hm
  have hc := congrArg (fun A => fun row => A row k) hm
  simp only [matrix_mul_stringWeyl_entry _ (geckStringLength_le_three P i j)] at hc
  change (adjointWeyl P b R i t).val.val *ᵥ
    (fun row => geckStringMatrixOver P b R i j h row k) = _ at hc
  have hv : (fun row => geckStringMatrixOver P b R i j h row k) =
      rootVector P b R j := by
    ext row
    simp only [geckStringMatrixOver, Matrix.map_apply, geckStringMatrix_entry, hk]
    rfl
  have hr : (fun row => geckStringMatrixOver P b R i j h row k.rev) =
      rootVector P b R (P.reflectionPerm i j) := by
    ext row
    simp only [geckStringMatrixOver, Matrix.map_apply, geckStringMatrix_entry,
      geckStringIndex_rev P b i j h k, hk]
    rfl
  rw [hv] at hc
  ext row
  have he := congrFun hc row
  simp only [hn] at he
  simpa only [← hr, Pi.smul_apply, smul_eq_mul, k, mul_comm, mul_left_comm,
    mul_assoc] using he

end Atlas.Chevalley

import Atlas.LinearGroups.Chevalley.Integral.RootStringWeyl

noncomputable section
namespace Atlas.Chevalley.Integral
variable {R : Type*} [CommRing R]

/-- The diagonal weight operator on a complete string. -/
def stringTorus (n : ℕ) (t : Rˣ) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  Matrix.diagonal (fun k => t.val^k.val * t.inv^(n-k.val))

/-- The signs of the two Weyl words cancel before any characteristic is chosen. -/
theorem stringWeyl_eq_torus_mul (n : ℕ) (hn : n ≤ 3) (t : Rˣ) :
    stringWeyl n t = stringTorus n t * stringWeyl n 1 := by
  ext i j
  rw [stringTorus, Matrix.diagonal_mul, stringWeyl_entry n hn,
    stringWeyl_entry n hn]
  by_cases h : i = j.rev
  · subst i
    simp only [ite_true, Units.val_one, show (1 : Rˣ).inv = 1 from rfl, one_pow, mul_one, Fin.val_rev, Nat.add_sub_add_right]
    have hj : n - (n-j.val) = j.val := by omega
    rw [hj]
    ring
  · simp [h]

/-- The checked exponentials supply an actual inverse for the string Weyl word. -/
def stringWeylUnit (n : ℕ) (t : Rˣ) : (Matrix (Fin (n+1)) (Fin (n+1)) R)ˣ :=
  stringRootElement n t.val *
    Units.map (Matrix.reindexRingEquiv R Fin.revPerm).toMonoidHom
      (stringRootElement n (-t.inv)) * stringRootElement n t.val

theorem stringWeylUnit_val (n : ℕ) (t : Rˣ) :
    (stringWeylUnit n t).val = stringWeyl n t := rfl

end Atlas.Chevalley.Integral

namespace Atlas.Chevalley.Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

/-- Actual adjoint torus action on the complete root-string inclusion. -/
theorem geckStringMatrixOver_torus (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (t : Rˣ) :
    (Atlas.Chevalley.adjointTorus P b R i t).val.val *
      geckStringMatrixOver P b R i j h =
    geckStringMatrixOver P b R i j h * stringTorus (geckStringLength P i j) t := by
  let C := geckStringMatrixOver P b R i j h
  let H := (Atlas.Chevalley.adjointTorus P b R i t).val.val
  let W := (Atlas.Chevalley.adjointWeyl P b R i t).val.val
  let W₁ := (Atlas.Chevalley.adjointWeyl P b R i 1).val.val
  let S := stringWeylUnit (geckStringLength P i j) (1 : Rˣ)
  have h₁ : W₁ * C = C * S.val := geckStringMatrixOver_weyl P b R i j h 1
  have ht : W * C = C * (stringTorus (geckStringLength P i j) t * S.val) := by
    change W * C = C * (stringTorus (geckStringLength P i j) t *
      stringWeyl (geckStringLength P i j) 1)
    rw [← stringWeyl_eq_torus_mul _ (geckStringLength_le_three P i j)]
    exact geckStringMatrixOver_weyl P b R i j h t
  have hc : H * W₁ = W := by
    have hg : Atlas.Chevalley.adjointTorus P b R i t *
        Atlas.Chevalley.adjointWeyl P b R i 1 =
        Atlas.Chevalley.adjointWeyl P b R i t := by
      simp [Atlas.Chevalley.adjointTorus, mul_assoc]
    exact congrArg (fun g => g.val.val) hg
  have he : (H*C)*S.val = (C*stringTorus (geckStringLength P i j) t)*S.val := by
    rw [Matrix.mul_assoc, ← h₁, ← Matrix.mul_assoc, hc, ht, Matrix.mul_assoc]
  have hh := congrArg (fun A => A*S.inv) he
  simpa only [Matrix.mul_assoc, S.val_inv, Matrix.mul_one] using hh

omit [P.IsReduced] in
/-- The integer weight agrees with the intrinsic root-coroot pairing. -/
theorem geckString_weight (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j])
    (k : Fin (geckStringLength P i j+1)) :
    (k.val : ℤ) - (geckStringLength P i j-k.val : ℕ) =
      P.pairingIn ℤ (geckStringIndex P i j h k) i := by
  have hc := P.chainBotCoeff_sub_chainTopCoeff
    (geckStringIndex_independent P i j h k)
  rw [geckStringIndex_bot P b i j h k, geckStringIndex_top P b i j h k] at hc
  exact hc

end Atlas.Chevalley.Integral

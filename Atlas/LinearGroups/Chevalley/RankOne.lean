import Atlas.LinearGroups.Chevalley.Adjoint
import Mathlib.Tactic.LinearCombination

/-! Integral special-column formulas and rank-one Geck Weyl words in every characteristic. -/

noncomputable section
open scoped Matrix
open RootPairing.GeckConstruction
namespace Atlas.Chevalley.Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

 theorem dividedPower_mulVec_zero (i : b.support) (n : ℕ)
    (a : b.support ⊕ ι → ℤ) (ha : raising P b i ^ n *ᵥ a = 0) :
    raisingDividedPower P b i n *ᵥ a = 0 := by
  have h := congrArg (fun A => A *ᵥ a) (factorial_smul_raisingDividedPower P b i n)
  rw [Matrix.smul_mulVec, ha] at h
  apply (smul_right_injective (M := (b.support ⊕ ι → ℤ))
    (by exact_mod_cast Nat.factorial_ne_zero n : (n.factorial : ℤ) ≠ 0))
  simpa using h

 theorem dividedPower_cartan (i j : b.support) (n : ℕ) :
    raisingDividedPower P b i n *ᵥ u j =
      if n = 0 then u j else if n = 1 then |b.cartanMatrix i j| • v b i.val else 0 := by
  by_cases h0 : n = 0
  · subst n
    simp only [raisingDividedPower_zero, Matrix.one_mulVec, ite_true]
  by_cases h1 : n = 1
  · subst n
    simpa only [raisingDividedPower_one, show (1 : ℕ) ≠ 0 by decide, ite_false, ite_true] using raising_cartan P b i j
  simp only [h0, h1, ite_false]
  apply dividedPower_mulVec_zero
  exact raising_pow_vec_zero_of_le P b i (u j) (by omega) (raising_sq_cartan P b i j)

 theorem dividedPower_positive (i : b.support) (n : ℕ) :
    raisingDividedPower P b i n *ᵥ v b i.val = if n = 0 then v b i.val else 0 := by
  by_cases h0 : n = 0
  · subst n
    simp only [raisingDividedPower_zero, Matrix.one_mulVec, ite_true]
  simp only [h0, ite_false]
  apply dividedPower_mulVec_zero
  apply raising_pow_vec_zero_of_le P b i (v b i.val) (by omega : 1 ≤ n)
  simpa using raising_positive_simple P b i

 theorem dividedPower_negative_sq (i : b.support) :
    let := P.indexNeg
    raisingDividedPower P b i 2 *ᵥ v b (-i.val) = v b i.val := by
  let := P.indexNeg
  have h := congrArg (fun A => A *ᵥ v b (-i.val))
    (factorial_smul_raisingDividedPower P b i 2)
  rw [Matrix.smul_mulVec, raising_sq_negative_simple] at h
  norm_num only [Nat.factorial, Nat.cast_ofNat] at h
  exact (smul_right_injective (M := (b.support ⊕ ι → ℤ))
    (by norm_num : (2 : ℤ) ≠ 0)) h

 theorem dividedPower_negative (i : b.support) (n : ℕ) :
    let := P.indexNeg
    raisingDividedPower P b i n *ᵥ v b (-i.val) =
      if n = 0 then v b (-i.val) else if n = 1 then u i else
      if n = 2 then v b i.val else 0 := by
  let := P.indexNeg
  dsimp only
  by_cases h0 : n = 0
  · subst n
    simp only [raisingDividedPower_zero, Matrix.one_mulVec, ite_true]
  by_cases h1 : n = 1
  · subst n
    simpa only [raisingDividedPower_one, show (1 : ℕ) ≠ 0 by decide, ite_false, ite_true] using raising_negative_simple P b i
  by_cases h2 : n = 2
  · subst n
    simpa only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
      ite_false, ite_true] using dividedPower_negative_sq P b i
  simp only [h0, h1, h2, ite_false]
  apply dividedPower_mulVec_zero
  exact raising_pow_vec_zero_of_le P b i (v b (-i.val)) (by omega)
    (raising_cube_negative_simple P b i)

variable (R : Type*) [CommRing R]

/-- Cartan basis vector after coefficient reduction. -/
def cartanVector (j : b.support) : b.support ⊕ ι → R := (Int.castRingHom R) ∘ u j

/-- Root basis vector after coefficient reduction. -/
def rootVector (j : ι) : b.support ⊕ ι → R := (Int.castRingHom R) ∘ v b j

 theorem raisingDividedOver_cartan (i j : b.support) (n : ℕ) :
    raisingDividedOver P b R i n *ᵥ cartanVector P b R j =
      if n = 0 then cartanVector P b R j else if n = 1 then
        ((|b.cartanMatrix i j| : ℤ) : R) • rootVector P b R i.val else 0 := by
  ext row
  change ((raisingDividedPower P b i n).map (Int.castRingHom R) *ᵥ
    ((Int.castRingHom R) ∘ u j)) row = _
  rw [← RingHom.map_mulVec, dividedPower_cartan]
  split_ifs <;> simp [cartanVector, rootVector, Pi.smul_apply, smul_eq_mul]

 theorem raisingDividedOver_positive (i : b.support) (n : ℕ) :
    raisingDividedOver P b R i n *ᵥ rootVector P b R i.val =
      if n = 0 then rootVector P b R i.val else 0 := by
  ext row
  change ((raisingDividedPower P b i n).map (Int.castRingHom R) *ᵥ
    ((Int.castRingHom R) ∘ v b i.val)) row = _
  rw [← RingHom.map_mulVec, dividedPower_positive]
  split_ifs <;> simp [rootVector]

 theorem raisingDividedOver_negative (i : b.support) (n : ℕ) :
    let := P.indexNeg
    raisingDividedOver P b R i n *ᵥ rootVector P b R (-i.val) =
      if n = 0 then rootVector P b R (-i.val) else if n = 1 then cartanVector P b R i else
      if n = 2 then rootVector P b R i.val else 0 := by
  let := P.indexNeg
  dsimp only
  ext row
  change ((raisingDividedPower P b i n).map (Int.castRingHom R) *ᵥ
    ((Int.castRingHom R) ∘ v b (-i.val))) row = _
  rw [← RingHom.map_mulVec, dividedPower_negative]
  split_ifs <;> simp [rootVector, cartanVector]

 theorem raisingExponential_cartan (i j : b.support) (t : R) :
    raisingExponential P b R i t *ᵥ cartanVector P b R j =
      cartanVector P b R j + (t * ((|b.cartanMatrix i j| : ℤ) : R)) • rootVector P b R i.val := by
  rw [raisingExponential_expansion]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, raisingDividedOver_cartan]
  norm_num [smul_smul]

 theorem raisingExponential_positive (i : b.support) (t : R) :
    raisingExponential P b R i t *ᵥ rootVector P b R i.val = rootVector P b R i.val := by
  rw [raisingExponential_expansion]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, raisingDividedOver_positive]
  norm_num

 theorem raisingExponential_negative (i : b.support) (t : R) :
    let := P.indexNeg
    raisingExponential P b R i t *ᵥ rootVector P b R (-i.val) =
      rootVector P b R (-i.val) + t • cartanVector P b R i + t^2 • rootVector P b R i.val := by
  let := P.indexNeg
  dsimp only
  rw [raisingExponential_expansion]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, raisingDividedOver_negative]
  norm_num


omit [P.IsCrystallographic] [P.IsReduced] in
 theorem oppositionOver_cartan (j : b.support) :
    oppositionOver P b R *ᵥ cartanVector P b R j = cartanVector P b R j := by
  have hu : ω b *ᵥ u j = u j := by
    ext (k | k) <;> simp [ω, u, Pi.single_apply, Matrix.one_apply]
  ext row
  change ((ω b).map (Int.castRingHom R) *ᵥ ((Int.castRingHom R) ∘ u j)) row = _
  rw [← RingHom.map_mulVec, hu]
  rfl

omit [P.IsCrystallographic] [P.IsReduced] in
 theorem oppositionOver_root (j : ι) :
    let := P.indexNeg
    oppositionOver P b R *ᵥ rootVector P b R j = rootVector P b R (-j) := by
  let := P.indexNeg
  dsimp only
  have hv : ω b *ᵥ v b j = v b (-j) := by
    ext (k | k) <;> simp [ω, v, Pi.single_apply, -RootPairing.indexNeg_neg]
  ext row
  change ((ω b).map (Int.castRingHom R) *ᵥ ((Int.castRingHom R) ∘ v b j)) row = _
  rw [← RingHom.map_mulVec, hv]
  rfl

 theorem loweringExponential_eq_conj (i : b.support) (t : R) :
    loweringExponential P b R i t =
      oppositionOver P b R * raisingExponential P b R i t * oppositionOver P b R := by
  rw [← loweringRootElement_val]
  rfl

 theorem loweringExponential_cartan (i j : b.support) (t : R) :
    let := P.indexNeg
    loweringExponential P b R i t *ᵥ cartanVector P b R j =
      cartanVector P b R j + (t * ((|b.cartanMatrix i j| : ℤ) : R)) • rootVector P b R (-i.val) := by
  let := P.indexNeg
  dsimp only
  rw [loweringExponential_eq_conj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    oppositionOver_cartan, raisingExponential_cartan, Matrix.mulVec_add,
    Matrix.mulVec_smul, oppositionOver_cartan, oppositionOver_root]

 theorem loweringExponential_negative (i : b.support) (t : R) :
    let := P.indexNeg
    loweringExponential P b R i t *ᵥ rootVector P b R (-i.val) = rootVector P b R (-i.val) := by
  let := P.indexNeg
  dsimp only
  rw [loweringExponential_eq_conj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    oppositionOver_root, neg_neg, raisingExponential_positive, oppositionOver_root]

 theorem loweringExponential_positive (i : b.support) (t : R) :
    let := P.indexNeg
    loweringExponential P b R i t *ᵥ rootVector P b R i.val =
      rootVector P b R i.val + t • cartanVector P b R i + t^2 • rootVector P b R (-i.val) := by
  let := P.indexNeg
  dsimp only
  rw [loweringExponential_eq_conj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    oppositionOver_root, raisingExponential_negative, Matrix.mulVec_add,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    oppositionOver_root, neg_neg, oppositionOver_cartan, oppositionOver_root]

end Atlas.Chevalley.Integral

namespace Atlas.Chevalley
open Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

/-- The pinned simple-reflection representative for any unit parameter. -/
def adjointWeyl (i : b.support) (t : Rˣ) : Adjoint P b R :=
  adjointX P b R i t.val * adjointY P b R i (-t.inv) * adjointX P b R i t.val

/-- The corresponding pinned torus word, before any structure theorem is assumed. -/
def adjointTorus (i : b.support) (t : Rˣ) : Adjoint P b R :=
  adjointWeyl P b R i t * (adjointWeyl P b R i 1)⁻¹

 theorem adjointWeyl_positive (i : b.support) (t : Rˣ) :
    let := P.indexNeg
    (adjointWeyl P b R i t).val.val *ᵥ rootVector P b R i.val =
      t.inv^2 • rootVector P b R (-i.val) := by
  let := P.indexNeg
  dsimp only
  change (raisingExponential P b R i t.val * (loweringRootElement P b R i (-t.inv)).val *
    raisingExponential P b R i t.val) *ᵥ rootVector P b R i.val = _
  rw [loweringRootElement_val, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    raisingExponential_positive, loweringExponential_positive]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, raisingExponential_positive,
    raisingExponential_cartan, raisingExponential_negative, b.cartanMatrix_apply_same]
  ext row
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  norm_num
  have h := t.val_inv
  linear_combination ((t.val*t.inv-1) * (rootVector P b R i.val row) +
    t.inv * (cartanVector P b R i row)) * h


 theorem adjointWeyl_negative (i : b.support) (t : Rˣ) :
    let := P.indexNeg
    (adjointWeyl P b R i t).val.val *ᵥ rootVector P b R (-i.val) =
      t.val^2 • rootVector P b R i.val := by
  let := P.indexNeg
  dsimp only
  change (raisingExponential P b R i t.val * (loweringRootElement P b R i (-t.inv)).val *
    raisingExponential P b R i t.val) *ᵥ rootVector P b R (-i.val) = _
  rw [loweringRootElement_val, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    raisingExponential_negative]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, loweringExponential_negative,
    loweringExponential_cartan, loweringExponential_positive,
    raisingExponential_positive, raisingExponential_cartan, raisingExponential_negative,
    b.cartanMatrix_apply_same]
  ext row
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  norm_num
  have h := t.val_inv
  linear_combination (t.val^2*(t.val*t.inv-3) * (rootVector P b R i.val row) +
    t.val*(t.val*t.inv-2) * (cartanVector P b R i row) +
    (t.val*t.inv-1) * (rootVector P b R (-i.val) row)) * h

 theorem adjointWeyl_cartan (i j : b.support) (t : Rˣ) :
    (adjointWeyl P b R i t).val.val *ᵥ cartanVector P b R j =
      cartanVector P b R j - ((|b.cartanMatrix i j| : ℤ) : R) • cartanVector P b R i := by
  let := P.indexNeg
  change (raisingExponential P b R i t.val * (loweringRootElement P b R i (-t.inv)).val *
    raisingExponential P b R i t.val) *ᵥ cartanVector P b R j = _
  rw [loweringRootElement_val, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    raisingExponential_cartan]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, loweringExponential_cartan,
    loweringExponential_positive, raisingExponential_positive, raisingExponential_cartan,
    raisingExponential_negative, b.cartanMatrix_apply_same]
  ext row
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  norm_num
  have h := t.val_inv
  linear_combination ((((|b.cartanMatrix i j| : ℤ) : R)) *
    ((t.val*t.inv-1) * (cartanVector P b R i row) +
    t.val*(t.val*t.inv-2) * (rootVector P b R i.val row) +
    t.inv * (rootVector P b R (-i.val) row))) * h

end Atlas.Chevalley

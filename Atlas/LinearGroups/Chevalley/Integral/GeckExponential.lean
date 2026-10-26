import Atlas.LinearGroups.Chevalley.Integral.GeckDividedPowers

/-! Faithful additive Geck root parametrizations obtained from integral divided powers. -/

noncomputable section
open scoped Matrix
open RootPairing.GeckConstruction
namespace Atlas.Chevalley.Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)


variable (R : Type*) [CommRing R]

/-- Integral Geck divided powers reduced to an arbitrary commutative ring. -/
def raisingDividedOver (i : b.support) (n : ℕ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  (raisingDividedPower P b i n).map (Int.castRingHom R)

@[simp] theorem raisingDividedOver_zero (i : b.support) :
    raisingDividedOver P b R i 0 = 1 := by
  simp [raisingDividedOver]

@[simp] theorem raisingDividedOver_one (i : b.support) :
    raisingDividedOver P b R i 1 = raisingOver P b R i := by
  simp [raisingDividedOver, raisingOver]

 theorem raisingDividedOver_eq_zero (i : b.support) (n : ℕ) (hn : 4 ≤ n) :
    raisingDividedOver P b R i n = 0 := by
  simp [raisingDividedOver, raisingDividedPower_eq_zero P b i n hn]

 theorem raisingDividedOver_mul (i : b.support) (k l : ℕ) :
    raisingDividedOver P b R i k * raisingDividedOver P b R i l =
      (((k+l).choose l : ℕ) : R) • raisingDividedOver P b R i (k+l) := by
  change (Int.castRingHom R).mapMatrix (raisingDividedPower P b i k) *
    (Int.castRingHom R).mapMatrix (raisingDividedPower P b i l) = _
  rw [← map_mul, raisingDividedPower_mul]
  ext row col
  change ((((((k+l).choose l : ℕ) : ℤ) • raisingDividedPower P b i (k+l)) row col) : R) = _
  rw [Matrix.smul_apply]
  simp [raisingDividedOver, smul_eq_mul]

/-- The actual Geck root exponential, formed integrally before coefficient reduction. -/
def raisingExponential (i : b.support) (t : R) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  ∑ k ∈ Finset.range 4, t ^ k • raisingDividedOver P b R i k

 theorem raisingExponential_expansion (i : b.support) (t : R) :
    raisingExponential P b R i t =
      raisingDividedOver P b R i 0 + t • raisingDividedOver P b R i 1 +
      t ^ 2 • raisingDividedOver P b R i 2 + t ^ 3 • raisingDividedOver P b R i 3 := by
  simp [raisingExponential, Finset.sum_range_succ]

@[simp] theorem raisingExponential_zero (i : b.support) :
    raisingExponential P b R i 0 = 1 := by
  simp [raisingExponential_expansion]

 theorem raisingExponential_add (i : b.support) (s t : R) :
    raisingExponential P b R i (s+t) =
      raisingExponential P b R i s * raisingExponential P b R i t := by
  rw [raisingExponential_expansion, raisingExponential_expansion,
    raisingExponential_expansion]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    raisingDividedOver_mul]
  norm_num [raisingDividedOver_eq_zero, Nat.choose]
  ext row col
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

 theorem raisingExponential_mul_neg (i : b.support) (t : R) :
    raisingExponential P b R i t * raisingExponential P b R i (-t) = 1 := by
  rw [← raisingExponential_add, add_neg_cancel, raisingExponential_zero]

 theorem raisingExponential_neg_mul (i : b.support) (t : R) :
    raisingExponential P b R i (-t) * raisingExponential P b R i t = 1 := by
  rw [← raisingExponential_add, neg_add_cancel, raisingExponential_zero]

/-- Invertible root elements in every characteristic, with no factorial division. -/
def raisingRootElement (i : b.support) (t : R) :
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ where
  val := raisingExponential P b R i t
  inv := raisingExponential P b R i (-t)
  val_inv := raisingExponential_mul_neg P b R i t
  inv_val := raisingExponential_neg_mul P b R i t

/-- The additive root parametrization for an actual Geck matrix. -/
def raisingRootHom (i : b.support) :
    Multiplicative R →* (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ where
  toFun t := raisingRootElement P b R i t.toAdd
  map_one' := by
    apply Units.ext
    exact raisingExponential_zero P b R i
  map_mul' s t := by
    apply Units.ext
    exact raisingExponential_add P b R i s.toAdd t.toAdd


 theorem raisingDividedPower_parameter_entry (i : b.support) (n : ℕ) :
    let := P.indexNeg
    raisingDividedPower P b i n (.inl i) (.inr (-i.val)) = if n = 1 then 1 else 0 := by
  let := P.indexNeg
  dsimp only
  have h1 := congrFun (raising_negative_simple P b i) (.inl i)
  have h2 := congrFun (raising_sq_negative_simple P b i) (.inl i)
  have h3 := congrFun (raising_cube_negative_simple P b i) (.inl i)
  simp only [v, u, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_eq_same,
    Pi.smul_apply, Pi.single_eq_of_ne (Sum.inl_ne_inr), smul_zero, Pi.zero_apply] at h1 h2 h3
  by_cases hn : n < 4
  · interval_cases n
    · simp
    · simpa using h1
    · simp only [raisingDividedPower, h2]
      norm_num
    · simp only [raisingDividedPower, h3]
      norm_num
  · rw [raisingDividedPower_eq_zero P b i n (by omega)]
    simp [show n ≠ 1 by omega]

 theorem raisingExponential_parameter_entry (i : b.support) (t : R) :
    let := P.indexNeg
    raisingExponential P b R i t (.inl i) (.inr (-i.val)) = t := by
  let := P.indexNeg
  dsimp only
  simp only [raisingExponential_expansion, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, raisingDividedOver, Matrix.map_apply,
    raisingDividedPower_parameter_entry]
  norm_num

 theorem raisingExponential_injective (i : b.support) :
    Function.Injective (raisingExponential P b R i) := by
  let := P.indexNeg
  intro s t h
  have hst := congrArg (fun A => A (.inl i) (.inr (-i.val))) h
  simpa only [raisingExponential_parameter_entry] using hst

 theorem raisingRootElement_injective (i : b.support) :
    Function.Injective (raisingRootElement P b R i) := by
  intro s t h
  exact raisingExponential_injective P b R i (congrArg Units.val h)

/-- The actual integral Geck involution, after scalar reduction. -/
def oppositionOver : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  (ω b).map (Int.castRingHom R)

omit [P.IsCrystallographic] [P.IsReduced] in
 theorem oppositionOver_mul_self : oppositionOver P b R * oppositionOver P b R = 1 := by
  change (Int.castRingHom R).mapMatrix (ω b) * (Int.castRingHom R).mapMatrix (ω b) = _
  rw [← map_mul, ω_mul_ω, map_one]

/-- The integral involution is a unit over every coefficient ring. -/
def oppositionUnit : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ where
  val := oppositionOver P b R
  inv := oppositionOver P b R
  val_inv := oppositionOver_mul_self P b R
  inv_val := oppositionOver_mul_self P b R

omit [P.IsReduced] in
 theorem oppositionOver_raisingOver (i : b.support) :
    oppositionOver P b R * raisingOver P b R i * oppositionOver P b R =
      loweringOver P b R i := by
  have h : ω b * raising P b i * ω b = lowering P b i := by
    rw [raising, lowering, ω_mul_e, mul_assoc, ω_mul_ω, mul_one]
  change (Int.castRingHom R).mapMatrix (ω b) *
    (Int.castRingHom R).mapMatrix (raising P b i) *
    (Int.castRingHom R).mapMatrix (ω b) = _
  rw [← map_mul, ← map_mul, h]
  rfl

/-- Lowering root elements obtained by the actual Geck opposition conjugation. -/
def loweringRootElement (i : b.support) (t : R) :
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ :=
  oppositionUnit P b R * raisingRootElement P b R i t * (oppositionUnit P b R)⁻¹

 theorem loweringRootElement_add (i : b.support) (s t : R) :
    loweringRootElement P b R i (s+t) =
      loweringRootElement P b R i s * loweringRootElement P b R i t := by
  have h : raisingRootElement P b R i (s+t) =
      raisingRootElement P b R i s * raisingRootElement P b R i t :=
    Units.ext (raisingExponential_add P b R i s t)
  simp only [loweringRootElement, h]
  simp only [mul_assoc, inv_mul_cancel_left]

 theorem loweringRootElement_injective (i : b.support) :
    Function.Injective (loweringRootElement P b R i) := by
  intro s t h
  apply raisingRootElement_injective P b R i
  exact mul_left_cancel (mul_right_cancel h)


/-- Integral lowering divided powers are conjugates by the actual Geck involution. -/
def loweringDividedPower (i : b.support) (n : ℕ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  ω b * raisingDividedPower P b i n * ω b

omit [P.IsReduced] in
 theorem opposition_raising_pow (i : b.support) (n : ℕ) :
    ω b * raising P b i ^ n * ω b = lowering P b i ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : ω b * raising P b i * ω b = lowering P b i := by
      rw [raising, lowering, ω_mul_e, mul_assoc, ω_mul_ω, mul_one]
    calc
      ω b * raising P b i ^ (n+1) * ω b =
          (ω b * raising P b i ^ n * ω b) * (ω b * raising P b i * ω b) := by
        simp only [pow_succ, mul_assoc]
        rw [← mul_assoc (ω b) (ω b), ω_mul_ω, one_mul]
      _ = _ := by rw [ih, h, pow_succ]

 theorem factorial_smul_loweringDividedPower (i : b.support) (n : ℕ) :
    (n.factorial : ℤ) • loweringDividedPower P b i n = lowering P b i ^ n := by
  dsimp only [loweringDividedPower]
  rw [← smul_mul_assoc, ← mul_smul_comm, factorial_smul_raisingDividedPower,
    opposition_raising_pow]

@[simp] theorem loweringDividedPower_zero (i : b.support) :
    loweringDividedPower P b i 0 = 1 := by
  simpa using factorial_smul_loweringDividedPower P b i 0

@[simp] theorem loweringDividedPower_one (i : b.support) :
    loweringDividedPower P b i 1 = lowering P b i := by
  simpa using factorial_smul_loweringDividedPower P b i 1

 theorem loweringDividedPower_eq_zero (i : b.support) (n : ℕ) (hn : 4 ≤ n) :
    loweringDividedPower P b i n = 0 := by
  simp [loweringDividedPower, raisingDividedPower_eq_zero P b i n hn]


/-- The lowering exponential is the scalar reduction of integral divided powers. -/
def loweringExponential (i : b.support) (t : R) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  ∑ k ∈ Finset.range 4, t ^ k •
    (loweringDividedPower P b i k).map (Int.castRingHom R)

 theorem loweringRootElement_val (i : b.support) (t : R) :
    (loweringRootElement P b R i t).val = loweringExponential P b R i t := by
  change oppositionOver P b R * raisingExponential P b R i t * oppositionOver P b R = _
  simp only [raisingExponential, loweringExponential, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  change (Int.castRingHom R).mapMatrix (ω b) *
    (Int.castRingHom R).mapMatrix (raisingDividedPower P b i k) *
    (Int.castRingHom R).mapMatrix (ω b) =
      (Int.castRingHom R).mapMatrix (ω b * raisingDividedPower P b i k * ω b)
  simp only [map_mul]

 theorem loweringExponential_add (i : b.support) (s t : R) :
    loweringExponential P b R i (s+t) =
      loweringExponential P b R i s * loweringExponential P b R i t := by
  simpa only [Units.val_mul, loweringRootElement_val] using
    congrArg Units.val (loweringRootElement_add P b R i s t)

 theorem loweringExponential_injective (i : b.support) :
    Function.Injective (loweringExponential P b R i) := by
  intro s t h
  apply loweringRootElement_injective P b R i
  apply Units.ext
  simpa only [loweringRootElement_val] using h

end Atlas.Chevalley.Integral

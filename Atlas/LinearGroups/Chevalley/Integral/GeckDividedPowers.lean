import Atlas.LinearGroups.Chevalley.Integral.Adjoint
import Mathlib.Data.Nat.Choose.Basic

/-! # Integral divided powers of the actual Geck raising operators

Root-string coefficients and special Cartan/root columns prove factorial
divisibility before integer matrix quotients are defined. No target-field
division or supplied integrality certificate is used. The uniform fourth-power
bound and divided-power multiplication law hold for every reduced integral
crystallographic pairing with its chosen base.
-/

noncomputable section
open scoped Matrix
open RootPairing.GeckConstruction
namespace Atlas.Chevalley.Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

omit [P.IsReduced] in
theorem raising_negative_simple (i : b.support) :
    let := P.indexNeg
    raising P b i *ᵥ v b (-i.val) = u i := by
  let := P.indexNeg
  ext (j | j)
  · simp [raising, e, u, v, Pi.single_apply]
  · simp [raising, e, u, v, P.ne_zero j]

theorem raising_positive_simple (i : b.support) :
    raising P b i *ᵥ v b i.val = 0 := by
  let := P.indexNeg
  have : Module.IsReflexive ℤ M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree ℤ M
  have hn : (i.val : ι) ≠ -i.val := RootPairing.ne_neg P i.val
  have hnr (j : ι) : P.root j ≠ P.root i + P.root i := by
    intro h
    apply P.nsmul_notMem_range_root (n := 2) (i := i.val)
    exact ⟨j, by simpa [two_smul] using h⟩
  ext (j | j)
  · simp [raising, e, v, -RootPairing.indexNeg_neg, hn]
  · simp [raising, e, v, hnr]

omit [P.IsReduced] in
theorem raising_cartan (i j : b.support) :
    raising P b i *ᵥ u j = |b.cartanMatrix i j| • v b i.val :=
  e_lie_u i j

theorem raising_sq_cartan (i j : b.support) :
    (raising P b i ^ 2) *ᵥ u j = 0 := by
  rw [pow_two, ← Matrix.mulVec_mulVec, raising_cartan, Matrix.mulVec_smul,
    raising_positive_simple, smul_zero]

omit [P.IsReduced] in
theorem raising_sq_negative_simple (i : b.support) :
    let := P.indexNeg
    (raising P b i ^ 2) *ᵥ v b (-i.val) = (2 : ℤ) • v b i.val := by
  let := P.indexNeg
  dsimp only
  rw [pow_two, ← Matrix.mulVec_mulVec, raising_negative_simple, raising_cartan,
    b.cartanMatrix_apply_same]
  norm_num

theorem raising_cube_negative_simple (i : b.support) :
    let := P.indexNeg
    (raising P b i ^ 3) *ᵥ v b (-i.val) = 0 := by
  let := P.indexNeg
  dsimp only
  rw [show (3 : ℕ) = 2+1 by rfl, pow_succ', ← Matrix.mulVec_mulVec,
    raising_sq_negative_simple, Matrix.mulVec_smul, raising_positive_simple, smul_zero]



omit [Fintype ι] [DecidableEq ι] [P.IsCrystallographic] [P.IsReduced] in
/-- Root-string translation preserves independence from its direction. -/
theorem shifted_root_independent {i j k : ι} (n : ℕ)
    (h : LinearIndependent ℤ ![P.root i, P.root j])
    (hk : P.root k = P.root j + n • P.root i) :
    LinearIndependent ℤ ![P.root i, P.root k] := by
  rw [hk, LinearIndependent.pair_iff]
  intro a c hac
  have he : (a + c * (n : ℤ)) • P.root i + c • P.root j = 0 := by
    calc
      _ = a • P.root i + c • (P.root j + n • P.root i) := by module
      _ = 0 := by simpa only [Int.cast_smul_eq_zsmul] using hac
  obtain ⟨ha, hc⟩ := (LinearIndependent.pair_iff.mp h) (a+c*(n : ℤ)) c (by
    simpa only [Int.cast_smul_eq_zsmul] using he)
  exact ⟨by simpa [hc] using ha, hc⟩

omit [P.IsReduced] in
/-- Exact coefficients of the actual Geck powers along an ordinary root string. -/
theorem raising_pow_root_and_bot (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (n : ℕ) (k : ι)
    (hk : P.root k = P.root j + n • P.root i) :
    P.chainBotCoeff i k = P.chainBotCoeff i j + n ∧
      (raising P b i ^ n) *ᵥ v b j =
        (((P.chainBotCoeff i j + 1).ascFactorial n : ℕ) : ℤ) • v b k := by
  induction n generalizing k with
  | zero =>
    have hkj : k = j := P.root.injective (by simpa using hk)
    subst k
    constructor
    · simp
    · ext r
      simp [v, Matrix.one_apply, Pi.single_apply]
  | succ n ih =>
    have hn : n ≤ P.chainTopCoeff i j := by
      have hn' : n+1 ≤ P.chainTopCoeff i j :=
        (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mp ⟨k, hk⟩
      omega
    obtain ⟨l, hl⟩ := (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr hn
    obtain ⟨hbot, hpow⟩ := ih l hl
    have hli : LinearIndependent ℤ ![P.root i, P.root l] :=
      shifted_root_independent P n h hl
    have hnext : P.root k = P.root l + P.root i := by
      rw [hk, hl]
      module
    constructor
    · rw [P.chainBotCoeff_of_add hli hnext, hbot]
      omega
    · rw [pow_succ', ← Matrix.mulVec_mulVec, hpow, Matrix.mulVec_smul]
      have he : raising P b i *ᵥ v b l =
          (P.chainBotCoeff i l + 1 : ℤ) • v b k :=
        e_lie_v_ne (by simpa [add_comm] using hnext)
      rw [he, smul_smul, hbot, Nat.ascFactorial_succ, Nat.cast_mul]
      congr 1
      push_cast
      rw [mul_comm]
      congr 1
      omega

omit [P.IsReduced] in
/-- Entrywise integral divisibility when the translated root exists. -/
theorem raising_pow_root_divided (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (n : ℕ) (k : ι)
    (hk : P.root k = P.root j + n • P.root i) :
    (raising P b i ^ n) *ᵥ v b j =
      (n.factorial : ℤ) •
        (((P.chainBotCoeff i j + n).choose n : ℕ) : ℤ) • v b k := by
  rw [(raising_pow_root_and_bot P b i j h n k hk).2,
    Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul, smul_smul]



omit [P.IsReduced] in
theorem raising_root_zero_of_not_add (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j])
    (hn : P.root i + P.root j ∉ Set.range P.root) :
    raising P b i *ᵥ v b j = 0 := by
  let := P.indexNeg
  have hj : j ≠ -i.val := by
    intro hj
    have hsame : LinearIndependent ℤ ![P.root i, P.root i] := by simpa [hj] using h
    have he := hsame.injective (show (![P.root i, P.root i] : Fin 2 → M) 0 =
      (![P.root i, P.root i] : Fin 2 → M) 1 from rfl)
    norm_num at he
  have hn' (k : ι) : P.root k ≠ P.root i + P.root j := fun hk => hn ⟨k, hk⟩
  ext (k | k)
  · simp [raising, e, v, -RootPairing.indexNeg_neg, hj]
  · simp [raising, e, v, hn']

omit [P.IsReduced] in
theorem raising_pow_root_zero (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (n : ℕ)
    (hn : P.chainTopCoeff i j < n) :
    (raising P b i ^ n) *ᵥ v b j = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn' : P.chainTopCoeff i j < n
    · rw [pow_succ', ← Matrix.mulVec_mulVec, ih hn', Matrix.mulVec_zero]
    · have hle : n ≤ P.chainTopCoeff i j := by omega
      obtain ⟨k, hk⟩ := (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr hle
      have hki := shifted_root_independent P n h hk
      have hnot : P.root i + P.root k ∉ Set.range P.root := by
        intro ⟨l, hl⟩
        have hnext : P.root j + (n+1) • P.root i ∈ Set.range P.root := by
          refine ⟨l, ?_⟩
          rw [hl, hk]
          module
        have := (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mp hnext
        omega
      rw [pow_succ', ← Matrix.mulVec_mulVec,
        (raising_pow_root_and_bot P b i j h n k hk).2,
        Matrix.mulVec_smul, raising_root_zero_of_not_add P b i k hki hnot, smul_zero]

theorem raising_four_eq_zero (i : b.support) : raising P b i ^ 4 = 0 := by
  let := P.indexNeg
  apply Matrix.ext
  intro row col
  have hcol : (raising P b i ^ 4) *ᵥ Pi.single col 1 = 0 := by
    rcases col with j | j
    · change (raising P b i ^ 4) *ᵥ u j = 0
      rw [show (4 : ℕ) = 2+2 by rfl, pow_add, ← Matrix.mulVec_mulVec,
        raising_sq_cartan, Matrix.mulVec_zero]
    · change (raising P b i ^ 4) *ᵥ v b j = 0
      by_cases hp : j = i.val
      · subst j
        rw [show (4 : ℕ) = 3+1 by rfl, pow_succ, ← Matrix.mulVec_mulVec,
          raising_positive_simple, Matrix.mulVec_zero]
      · by_cases hm : j = -i.val
        · subst j
          rw [show (4 : ℕ) = 3+1 by rfl, pow_succ', ← Matrix.mulVec_mulVec,
            raising_cube_negative_simple, Matrix.mulVec_zero]
        · have hlin : LinearIndependent ℤ ![P.root i, P.root j] := by
            apply RootPairing.IsReduced.linearIndependent P
            · intro hh
              exact hp hh.symm
            · intro hh
              rw [P.root_eq_neg_iff] at hh
              change i.val = -j at hh
              exact hm (by simpa only [neg_neg] using congrArg Neg.neg hh.symm)
          apply raising_pow_root_zero P b i j hlin
          have hbound := P.chainBotCoeff_add_chainTopCoeff_le_three (i := i.val) (j := j)
          omega
  have hrow := congrFun hcol row
  simpa using hrow



omit [P.IsReduced] in
theorem raising_pow_vec_zero_of_le (i : b.support) (x : b.support ⊕ ι → ℤ)
    {k n : ℕ} (hkn : k ≤ n) (hk : (raising P b i ^ k) *ᵥ x = 0) :
    (raising P b i ^ n) *ᵥ x = 0 := by
  calc
    (raising P b i ^ n) *ᵥ x =
      (raising P b i ^ (n-k)) *ᵥ ((raising P b i ^ k) *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, ← pow_add, Nat.sub_add_cancel hkn]
    _ = 0 := by rw [hk, Matrix.mulVec_zero]

/-- Factorial divisibility of every entry of the actual integral Geck powers. -/
theorem factorial_dvd_raising_pow_entry (i : b.support) (n : ℕ)
    (row col : b.support ⊕ ι) :
    (n.factorial : ℤ) ∣ (raising P b i ^ n) row col := by
  let := P.indexNeg
  by_cases hn : n < 2
  · interval_cases n <;> simp
  have hn : 2 ≤ n := by omega
  suffices (n.factorial : ℤ) ∣ ((raising P b i ^ n) *ᵥ Pi.single col 1) row by
    simpa using this
  rcases col with j | j
  · change (n.factorial : ℤ) ∣ ((raising P b i ^ n) *ᵥ u j) row
    rw [raising_pow_vec_zero_of_le P b i (u j) hn (raising_sq_cartan P b i j)]
    simp
  · change (n.factorial : ℤ) ∣ ((raising P b i ^ n) *ᵥ v b j) row
    by_cases hp : j = i.val
    · subst j
      rw [raising_pow_vec_zero_of_le P b i (v b i.val) (by omega : 1 ≤ n)
        (by simpa using raising_positive_simple P b i)]
      simp
    · by_cases hm : j = -i.val
      · subst j
        by_cases htwo : n = 2
        · subst n
          rw [raising_sq_negative_simple]
          simp
        · rw [raising_pow_vec_zero_of_le P b i (v b (-i.val)) (by omega : 3 ≤ n)
            (raising_cube_negative_simple P b i)]
          simp
      · have hlin : LinearIndependent ℤ ![P.root i, P.root j] := by
          apply RootPairing.IsReduced.linearIndependent P
          · intro hh
            exact hp hh.symm
          · intro hh
            rw [P.root_eq_neg_iff] at hh
            change i.val = -j at hh
            exact hm (by simpa only [neg_neg] using congrArg Neg.neg hh.symm)
        by_cases hex : P.root j + n • P.root i ∈ Set.range P.root
        · obtain ⟨k, hk⟩ := hex
          rw [raising_pow_root_divided P b i j hlin n k hk]
          exact dvd_mul_right _ _
        · have htop : P.chainTopCoeff i j < n := by
            have := (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).not.mp hex
            omega
          rw [raising_pow_root_zero P b i j hlin n htop]
          simp

/-- Integral matrix quotient, justified entrywise by proved factorial divisibility.
Reduction to any target field is performed only after this integral construction. -/
def raisingDividedPower (i : b.support) (n : ℕ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  fun row col => (raising P b i ^ n) row col / (n.factorial : ℤ)

theorem factorial_smul_raisingDividedPower (i : b.support) (n : ℕ) :
    (n.factorial : ℤ) • raisingDividedPower P b i n = raising P b i ^ n := by
  ext row col
  exact Int.mul_ediv_cancel' (factorial_dvd_raising_pow_entry P b i n row col)



@[simp] theorem raisingDividedPower_zero (i : b.support) :
    raisingDividedPower P b i 0 = 1 := by
  simpa using factorial_smul_raisingDividedPower P b i 0

@[simp] theorem raisingDividedPower_one (i : b.support) :
    raisingDividedPower P b i 1 = raising P b i := by
  simpa using factorial_smul_raisingDividedPower P b i 1

theorem raisingDividedPower_eq_zero (i : b.support) (n : ℕ) (hn : 4 ≤ n) :
    raisingDividedPower P b i n = 0 := by
  have hz : raising P b i ^ n = 0 := pow_eq_zero_of_le hn (raising_four_eq_zero P b i)
  ext row col
  simp [raisingDividedPower, hz]

/-- The actual integral Geck divided powers satisfy the binomial product law. -/
theorem raisingDividedPower_mul (i : b.support) (k l : ℕ) :
    raisingDividedPower P b i k * raisingDividedPower P b i l =
      (((k+l).choose l : ℕ) : ℤ) • raisingDividedPower P b i (k+l) := by
  have hsc : (k.factorial : ℤ) * (l.factorial : ℤ) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero k)
      (by exact_mod_cast Nat.factorial_ne_zero l)
  apply (smul_right_injective (M := Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) hsc)
  calc
    ((k.factorial : ℤ) * (l.factorial : ℤ)) •
        (raisingDividedPower P b i k * raisingDividedPower P b i l) =
        ((k.factorial : ℤ) • raisingDividedPower P b i k) *
        ((l.factorial : ℤ) • raisingDividedPower P b i l) := by
      rw [smul_mul_smul_comm]
    _ = raising P b i ^ k * raising P b i ^ l := by
      rw [factorial_smul_raisingDividedPower, factorial_smul_raisingDividedPower]
    _ = raising P b i ^ (k+l) := (pow_add _ _ _).symm
    _ = ((k+l).factorial : ℤ) • raisingDividedPower P b i (k+l) :=
      (factorial_smul_raisingDividedPower P b i (k+l)).symm
    _ = _ := by
      dsimp only
      rw [smul_smul]
      congr 1
      exact_mod_cast (by simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Nat.add_choose_mul_factorial_mul_factorial k l).symm)

end Atlas.Chevalley.Integral

import Atlas.LinearGroups.Unitary.Hermitian
import Atlas.FieldTheory.FiniteQuadraticFibers

/-! # Actual norm fibres of standard Hermitian coordinate spaces -/
noncomputable section
namespace Atlas.Unitary
open Atlas.FiniteQuadratic
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- The value of the standard Hermitian norm in the base field. -/
def vectorNorm {n : ℕ} (v : Fin n → K) : F := ∑ i, norm F K (v i)

/-- The number of actual vectors of a prescribed Hermitian norm. -/
def normCount (n : ℕ) (a : F) : ℕ := Nat.card {v : Fin n → K // vectorNorm F K v = a}

variable {F K}
theorem vectorNorm_algebraMap (hdeg : Module.finrank F K = 2) {n : ℕ}
    (v : Fin n → K) : algebraMap F K (vectorNorm F K v) = hermitian F K v v := by
  simp [vectorNorm, hermitian, map_sum, norm_formula hdeg]

omit [Finite F] [Finite K] in
theorem vectorNorm_smul {n : ℕ} (c : K) (v : Fin n → K) :
    vectorNorm F K (c • v) = norm F K c * vectorNorm F K v := by
  simp [vectorNorm, map_mul, Finset.mul_sum]

omit [Finite F] [Finite K] in
theorem vectorNorm_cons {n : ℕ} (x : K) (v : Fin n → K) :
    vectorNorm F K (Fin.cons x v) = norm F K x + vectorNorm F K v := by
  simp [vectorNorm, Fin.sum_univ_succ]

/-- Scaling by an actual element of prescribed norm identifies nonzero fibres. -/
def normFiberEquiv (_hdeg : Module.finrank F K = 2) (n : ℕ)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : Fin n → K // vectorNorm F K v = a} ≃
      {v : Fin n → K // vectorNorm F K v = b} := by
  let he := norm_units_surjective F K (Units.mk0 (b / a) (div_ne_zero hb ha))
  let c := Classical.choose he
  have hc := Classical.choose_spec he
  have hc' : norm F K (c : K) = b / a := congrArg Units.val hc
  refine {
    toFun := fun v => ⟨(c : K) • v.val, ?_⟩
    invFun := fun v => ⟨((c⁻¹ : Kˣ) : K) • v.val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [vectorNorm_smul, v.prop, hc', div_mul_cancel₀ _ ha]
  · rw [vectorNorm_smul, v.prop]
    have hi : norm F K ((c⁻¹ : Kˣ) : K) = (b / a)⁻¹ := by
      have hu := congrArg Units.val ((Units.map (norm F K)).map_inv c)
      simpa only [Units.val_inv_eq_inv_val, Units.coe_map, hc'] using hu
    rw [hi]
    field_simp
  · intro v
    apply Subtype.ext
    simp [smul_smul]
  · intro v
    apply Subtype.ext
    simp [smul_smul]

theorem normCount_nonzero (hdeg : Module.finrank F K = 2) (n : ℕ)
    (a : F) (ha : a ≠ 0) : normCount F K n a = normCount F K n 1 :=
  Nat.card_congr (normFiberEquiv hdeg n a 1 ha one_ne_zero)

/-- Splitting the first coordinate gives the full, unweighted fibre recursion. -/
def normFiberSuccEquiv (n : ℕ) (a : F) :
    {v : Fin (n + 1) → K // vectorNorm F K v = a} ≃
      (x : K) × {v : Fin n → K // vectorNorm F K v = a - norm F K x} := {
  toFun := fun v => ⟨v.val 0, Fin.tail v.val, by
    have h := v.prop
    rw [show v.val = Fin.cons (v.val 0) (Fin.tail v.val) from (Fin.cons_self_tail _).symm,
      vectorNorm_cons] at h
    linear_combination h⟩
  invFun := fun v => ⟨Fin.cons v.1 v.2.val, by
    rw [vectorNorm_cons, v.2.prop]
    ring⟩
  left_inv := fun v => Subtype.ext (Fin.cons_self_tail _)
  right_inv := fun v => by cases v; rfl }

theorem normCount_succ [Fintype K] (n : ℕ) (a : F) :
    normCount F K (n + 1) a = ∑ x : K, normCount F K n (a - norm F K x) := by
  exact (Nat.card_congr (normFiberSuccEquiv n a)).trans Nat.card_sigma


theorem normCount_sum [Fintype F] (hdeg : Module.finrank F K = 2) (n : ℕ) :
    ∑ a : F, normCount F K n a = (Nat.card F ^ 2) ^ n := by
  unfold normCount
  rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv (vectorNorm F K)),
    Nat.card_fun, Nat.card_fin, card_extension hdeg]

theorem normCount_total (hdeg : Module.finrank F K = 2) (n : ℕ) :
    normCount F K n 0 + (Nat.card F - 1) * normCount F K n 1 =
      (Nat.card F ^ 2) ^ n := by
  classical
  let := Fintype.ofFinite F
  have h := normCount_sum hdeg n
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))] at h
  have hs : ∑ a ∈ Finset.univ.erase (0 : F), normCount F K n a =
      (Nat.card F - 1) * normCount F K n 1 := by
    calc
      _ = ∑ _a ∈ Finset.univ.erase (0 : F), normCount F K n 1 :=
        Finset.sum_congr rfl (fun a ha => normCount_nonzero hdeg n a (Finset.mem_erase.mp ha).1)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  rw [hs] at h
  exact h

theorem normCount_succ_zero (hdeg : Module.finrank F K = 2) (n : ℕ) :
    normCount F K (n + 1) 0 = normCount F K n 0 +
      (Nat.card F ^ 2 - 1) * normCount F K n 1 := by
  classical
  let := Fintype.ofFinite K
  rw [normCount_succ, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K))]
  have hn : norm F K 0 = 0 := (norm_zero_iff hdeg 0).mpr rfl
  simp only [hn, sub_zero]
  congr 1
  calc
    _ = ∑ _x ∈ Finset.univ.erase (0 : K), normCount F K n 1 := by
      apply Finset.sum_congr rfl
      intro x hx
      apply normCount_nonzero hdeg
      simpa only [zero_sub, neg_ne_zero] using
        (mt (norm_zero_iff hdeg x).mp (Finset.mem_erase.mp hx).1)
    _ = _ := by simp [← Nat.card_eq_fintype_card, card_extension hdeg]

/-- A positive recurrence avoiding division and signed natural expressions. -/
theorem normCount_succ_one_recurrence (hdeg : Module.finrank F K = 2) (n : ℕ) :
    normCount F K (n + 1) 1 + Nat.card F * normCount F K n 1 =
      (Nat.card F + 1) * (Nat.card F ^ 2) ^ n := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqsub : Nat.card F - 1 + 1 = Nat.card F := Nat.sub_add_cancel (by omega)
  have hq2sub : Nat.card F ^ 2 - 1 + 1 = Nat.card F ^ 2 :=
    Nat.sub_add_cancel (by nlinarith)
  have h0 := normCount_total hdeg n
  have h1 := normCount_total hdeg (n + 1)
  have hz := normCount_succ_zero hdeg n
  rw [pow_succ] at h1
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card F - 1 by omega)
  zify at h0 h1 hz ⊢
  push_cast [Nat.cast_sub (show 1 ≤ Nat.card F by omega),
    Nat.cast_sub (show 1 ≤ Nat.card F ^ 2 by nlinarith)] at h0 h1 hz ⊢
  linear_combination h1 - hz - h0

omit [Finite F] [Finite K] in
theorem normCount_dim_zero_one : normCount F K 0 1 = 0 := by
  classical
  have : IsEmpty {v : Fin 0 → K // vectorNorm F K v = 1} := ⟨by
    intro v
    have h := v.prop
    simp [vectorNorm] at h⟩
  simp [normCount]

/-- The closed norm-one count, written over the integers to display the sign. -/
theorem normCount_one_int (hdeg : Module.finrank F K = 2) (n : ℕ) :
    (normCount F K (n + 1) 1 : ℤ) =
      (Nat.card F : ℤ) ^ n * ((Nat.card F : ℤ) ^ (n + 1) - (-1 : ℤ) ^ (n + 1)) := by
  induction n with
  | zero =>
    have h := normCount_succ_one_recurrence hdeg 0
    rw [normCount_dim_zero_one] at h
    simpa using congrArg (fun x : ℕ => (x : ℤ)) h
  | succ n ih =>
    have h := congrArg (fun x : ℕ => (x : ℤ))
      (normCount_succ_one_recurrence hdeg (n + 1))
    push_cast at h
    rw [ih] at h
    have hp : ((Nat.card F : ℤ) ^ 2) ^ (n + 1) =
        (Nat.card F : ℤ) ^ (n + 1) * (Nat.card F : ℤ) ^ (n + 1) := by ring
    rw [hp] at h
    simp only [pow_succ] at h ⊢
    linear_combination h

theorem orderFactor_int (q i : ℕ) (hq : 1 ≤ q) :
    (orderFactor q i : ℤ) = (q : ℤ) ^ i - (-1 : ℤ) ^ i := by
  unfold orderFactor
  rw [neg_one_pow_eq_ite]
  split_ifs with h
  · rw [Nat.cast_sub (one_le_pow₀ hq), Nat.cast_pow, Nat.cast_one]
  · push_cast
    ring

/-- Uniform norm-one vector count, valid also in characteristic two. -/
theorem normCount_one (hdeg : Module.finrank F K = 2) (n : ℕ) :
    normCount F K (n + 1) 1 = Nat.card F ^ n * orderFactor (Nat.card F) (n + 1) := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_mul, Nat.cast_pow, orderFactor_int _ _ (by omega)]
  exact normCount_one_int hdeg n

/-- Closed zero-norm count; it includes the zero vector. -/
theorem normCount_zero_int (hdeg : Module.finrank F K = 2) (n : ℕ) :
    (normCount F K (n + 1) 0 : ℤ) =
      (Nat.card F : ℤ) ^ (2 * n + 1) +
        ((Nat.card F : ℤ) - 1) * (-1 : ℤ) ^ (n + 1) * (Nat.card F : ℤ) ^ n := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have h := congrArg (fun x : ℕ => (x : ℤ)) (normCount_total hdeg (n + 1))
  push_cast [Nat.cast_sub (show 1 ≤ Nat.card F by omega)] at h
  rw [normCount_one_int hdeg n] at h
  have hp : ((Nat.card F : ℤ) ^ 2) ^ (n + 1) =
      (Nat.card F : ℤ) ^ (n + 1) * (Nat.card F : ℤ) ^ (n + 1) := by ring
  rw [hp] at h
  rw [pow_add, pow_mul]
  simp only [pow_succ] at h ⊢
  linear_combination h

/-- The counted base-field fibre is precisely the public Hermitian fibre. -/
theorem card_hermitian_self_fiber (hdeg : Module.finrank F K = 2) (n : ℕ) (a : F) :
    Nat.card {v : Fin n → K // hermitian F K v v = algebraMap F K a} =
      normCount F K n a := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro v
  rw [← vectorNorm_algebraMap hdeg]
  exact (algebraMap F K).injective.eq_iff

theorem card_hermitian_norm_one (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Nat.card {v : Fin (n + 1) → K // hermitian F K v v = 1} =
      Nat.card F ^ n * orderFactor (Nat.card F) (n + 1) := by
  simpa only [map_one] using
    (card_hermitian_self_fiber hdeg (n + 1) 1).trans (normCount_one hdeg n)

end Atlas.Unitary





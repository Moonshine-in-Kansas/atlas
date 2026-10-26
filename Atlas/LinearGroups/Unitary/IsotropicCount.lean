import Atlas.LinearGroups.Unitary.IsotropicAction
import Atlas.LinearGroups.Unitary.NormCounts
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-! # Counting actual isotropic projective lines -/
noncomputable section
namespace Atlas.Unitary
open Atlas.FiniteQuadratic
open scoped LinearAlgebra.Projectivization
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

def NonzeroIsotropicVectors (F K : Type*) [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (n : ℕ) := {v : Fin n → K // v ≠ 0 ∧ hermitian F K v v = 0}

/-- Choose a representative of each actual projective point and multiply by a
nonzero scalar. All vectors on that line are retained, with unique scalar. -/
def isotropicRepresentativeMap : IsotropicPoints F K n × Kˣ → NonzeroIsotropicVectors F K n :=
  fun p => ⟨p.2 • p.1.val.rep,
    smul_ne_zero p.2.ne_zero p.1.val.rep_nonzero, by
      simp [Units.smul_def, hermitian_smul_left, hermitian_smul_right, isotropic_rep]⟩

theorem isotropicRepresentativeMap_point (p : IsotropicPoints F K n × Kˣ) :
    Projectivization.mk K (isotropicRepresentativeMap p).val
      (isotropicRepresentativeMap p).prop.1 = p.1.val := by
  rw [← Projectivization.mk_rep p.1.val, Projectivization.mk_eq_mk_iff]
  exact ⟨p.2, rfl⟩

theorem isotropicRepresentativeMap_bijective :
    Function.Bijective (isotropicRepresentativeMap (F := F) (K := K) (n := n)) := by
  constructor
  · intro a b hab
    have hp : a.1 = b.1 := by
      apply Subtype.ext
      rw [← isotropicRepresentativeMap_point a, ← isotropicRepresentativeMap_point b]
      congr 1
      exact congrArg Subtype.val hab
    rcases a with ⟨p, a⟩
    rcases b with ⟨r, b⟩
    dsimp at hp
    subst r
    congr 1
    apply Units.ext
    have h := congrArg Subtype.val hab
    exact smul_left_injective K p.val.rep_nonzero h
  · intro v
    let p := isotropicPoint v.val v.prop.1 v.prop.2
    have hp : Projectivization.mk K v.val v.prop.1 =
        Projectivization.mk K p.val.rep p.val.rep_nonzero := by
      rw [Projectivization.mk_rep]
      rfl
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp hp
    exact ⟨(p, a), Subtype.ext ha⟩

def isotropicRepresentativeEquiv :
    IsotropicPoints F K n × Kˣ ≃ NonzeroIsotropicVectors F K n :=
  Equiv.ofBijective isotropicRepresentativeMap isotropicRepresentativeMap_bijective

theorem card_nonzero_isotropic (hdeg : Module.finrank F K = 2) :
    Nat.card (NonzeroIsotropicVectors F K n) =
      Nat.card (IsotropicPoints F K n) * (Nat.card F ^ 2 - 1) := by
  rw [← Nat.card_congr (isotropicRepresentativeEquiv (F := F) (K := K) (n := n)),
    Nat.card_prod, Nat.card_units, card_extension hdeg]

theorem card_nonzero_isotropic_eq_normCount (hdeg : Module.finrank F K = 2) :
    Nat.card (NonzeroIsotropicVectors F K n) = normCount F K n 0 - 1 := by
  classical
  let Z := {v : Fin n → K // hermitian F K v v = 0}
  let z : Z := ⟨0, hermitian_zero_left 0⟩
  let e : NonzeroIsotropicVectors F K n ≃ {w : Z // w ≠ z} := {
    toFun := fun v => ⟨⟨v.val, v.prop.2⟩, fun he => v.prop.1 (congrArg Subtype.val he)⟩
    invFun := fun w => ⟨w.val.val, fun he => w.prop (Subtype.ext he), w.val.prop⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  have hc : Nat.card {w : Z // w ≠ z} = Nat.card Z - 1 := by
    let := Fintype.ofFinite Z
    simp [Nat.card_eq_fintype_card]
  rw [hc]
  congr 1
  simpa only [map_zero] using card_hermitian_self_fiber hdeg n 0

/-- Fraction-free count obtained from the actual nonzero vector fibres. -/
theorem isotropic_count_mul (hdeg : Module.finrank F K = 2) :
    Nat.card (IsotropicPoints F K n) * (Nat.card F ^ 2 - 1) = normCount F K n 0 - 1 := by
  rw [← card_nonzero_isotropic hdeg, card_nonzero_isotropic_eq_normCount hdeg]

/-- The exact fibre denominator is q²−1, the number of nonzero extension scalars. -/
theorem isotropic_count_quotient (hdeg : Module.finrank F K = 2) :
    Nat.card (IsotropicPoints F K n) = (normCount F K n 0 - 1) / (Nat.card F ^ 2 - 1) := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hsq : 1 < Nat.card F ^ 2 := by nlinarith
  have hden : 0 < Nat.card F ^ 2 - 1 := by omega
  rw [← isotropic_count_mul hdeg]
  exact (Nat.mul_div_cancel _ hden).symm

theorem normCount_zero_factorization (hdeg : Module.finrank F K = 2) (n : ℕ) :
    normCount F K (n + 1) 0 =
      orderFactor (Nat.card F) (n + 1) * orderFactor (Nat.card F) n + 1 := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [normCount_zero_int hdeg n, orderFactor_int _ _ (by omega),
    orderFactor_int _ _ (by omega)]
  have hs : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by rw [← mul_pow]; simp
  simp only [pow_succ]
  rw [show 2 * n = n * 2 by omega, pow_mul, pow_two]
  linear_combination hs

/-- The uniform isotropic line count, including all small fields. -/
theorem card_isotropicPoints (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Nat.card (IsotropicPoints F K (n + 1)) =
      (orderFactor (Nat.card F) (n + 1) * orderFactor (Nat.card F) n) /
        (Nat.card F ^ 2 - 1) := by
  rw [isotropic_count_quotient hdeg, normCount_zero_factorization hdeg n,
    Nat.add_sub_cancel]

theorem card_isotropicPoints_mul (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Nat.card (IsotropicPoints F K (n + 1)) * (Nat.card F ^ 2 - 1) =
      orderFactor (Nat.card F) (n + 1) * orderFactor (Nat.card F) n := by
  rw [isotropic_count_mul hdeg, normCount_zero_factorization hdeg n, Nat.add_sub_cancel]

theorem card_isotropicPoints_dim_three (hdeg : Module.finrank F K = 2) :
    Nat.card (IsotropicPoints F K 3) = Nat.card F ^ 3 + 1 := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hsq : 1 < Nat.card F ^ 2 := by nlinarith
  have h := card_isotropicPoints_mul hdeg 2
  norm_num [orderFactor] at h
  exact h.resolve_right (by omega)

theorem card_isotropicPoints_dim_two (hdeg : Module.finrank F K = 2) :
    Nat.card (IsotropicPoints F K 2) = Nat.card F + 1 := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hsq : 1 < Nat.card F ^ 2 := by nlinarith
  have h := card_isotropicPoints_mul hdeg 1
  norm_num [orderFactor] at h
  rw [mul_comm (Nat.card F ^ 2 - 1)] at h
  exact Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card F ^ 2 - 1 by omega) h

end Atlas.Unitary




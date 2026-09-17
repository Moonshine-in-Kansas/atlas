import Atlas.LinearGroups.Orthogonal.CompensatedTorus
import Atlas.LinearGroups.Orthogonal.StandardComplement
import Atlas.LinearAlgebra.QuadraticScalar

/-! # The split negative scalar as a product of actual hyperbolic sign tori -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {n : ℕ} {F : Type*} [Field F]

def signTorusD (i : Fin n) : isometrySubgroup (formD n F) :=
  hyperbolicTorus _ (e i) (f i) (formD_e i) (formD_f i) (polarD_ef i)
    (-1) (neg_ne_zero.mpr one_ne_zero)

theorem signTorusD_e (i j : Fin n) :
    (signTorusD (F := F) i).val (e j) = if j = i then -e j else e j := by
  classical
  by_cases h : j = i
  · subst j
    rw [if_pos rfl]
    exact (hyperbolicTorus_e _ _ _ _ _ _ _ _).trans (neg_one_smul F _)
  · rw [if_neg h]
    apply hyperbolicTorus_perp _ _ _ _ _ _ _ _ (⟨e j, ?_, ?_⟩ : complement (formD n F) (e i) (f i))
    · change (formD n F).polarBilin (e j) (e i) = 0
      rw [polarD_e]
      simp [e, Pi.single_apply]
    · change (formD n F).polarBilin (e j) (f i) = 0
      rw [polarD_f]
      simp [e, Pi.single_apply, h, Ne.symm h]

theorem signTorusD_f (i j : Fin n) :
    (signTorusD (F := F) i).val (f j) = if j = i then -f j else f j := by
  classical
  by_cases h : j = i
  · subst j
    rw [if_pos rfl]
    have ht := hyperbolicTorus_f (formD n F) (e i) (f i) (formD_e i) (formD_f i)
      (polarD_ef i) (-1) (neg_ne_zero.mpr one_ne_zero)
    simpa only [signTorusD, inv_neg, inv_one, neg_one_smul] using ht
  · rw [if_neg h]
    apply hyperbolicTorus_perp _ _ _ _ _ _ _ _ (⟨f j, ?_, ?_⟩ : complement (formD n F) (e i) (f i))
    · change (formD n F).polarBilin (f j) (e i) = 0
      rw [polarD_e]
      simp [f, Pi.single_apply, h, Ne.symm h]
    · change (formD n F).polarBilin (f j) (f i) = 0
      rw [polarD_f]
      simp [f, Pi.single_apply]

def signProductD (l : List (Fin n)) : isometrySubgroup (formD n F) :=
  (l.map (signTorusD (F := F))).prod

theorem signProductD_e (l : List (Fin n)) (j : Fin n) :
    (signProductD (F := F) l).val (e j) = (-1 : F)^(l.count j) • e j := by
  classical
  induction l with
  | nil => simp [signProductD]
  | cons i l ih =>
    change (signTorusD (F := F) i).val ((signProductD (F := F) l).val (e j)) = _
    rw [ih, map_smul, signTorusD_e]
    by_cases h : j = i
    · subst i
      simp only [ite_true, List.count_cons_self, pow_succ, smul_neg, neg_one_mul,
        mul_neg_one, neg_smul]
    · simp [List.count_cons, h, Ne.symm h]

theorem signProductD_f (l : List (Fin n)) (j : Fin n) :
    (signProductD (F := F) l).val (f j) = (-1 : F)^(l.count j) • f j := by
  classical
  induction l with
  | nil => simp [signProductD]
  | cons i l ih =>
    change (signTorusD (F := F) i).val ((signProductD (F := F) l).val (f j)) = _
    rw [ih, map_smul, signTorusD_f]
    by_cases h : j = i
    · subst i
      simp only [ite_true, List.count_cons_self, pow_succ, smul_neg, neg_one_mul,
        mul_neg_one, neg_smul]
    · simp [List.count_cons, h, Ne.symm h]

def negativeScalarD (n : ℕ) (F : Type*) [Field F] : isometrySubgroup (formD n F) :=
  (isometryCarrierEquiv _).symm (scalarIsometry (formD n F) (-1) (by ring))

/-- This identity concerns the actual full linear isometries on the standard coordinates. -/
theorem negativeScalarD_eq_signProduct :
    negativeScalarD n F = signProductD (Finset.univ.toList : List (Fin n)) := by
  classical
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun F (Index n)).ext
  intro j
  rw [Pi.basisFun_apply]
  cases j with
  | inl i =>
    change (-1 : F) • e i = (signProductD (F := F) (Finset.univ.toList : List (Fin n))).val (e i)
    rw [signProductD_e, (Finset.nodup_toList _).count_of_mem (by simp), pow_one, neg_one_smul]
  | inr i =>
    change (-1 : F) • f i = (signProductD (F := F) (Finset.univ.toList : List (Fin n))).val (f i)
    rw [signProductD_f, (Finset.nodup_toList _).count_of_mem (by simp), pow_one, neg_one_smul]

theorem signProductD_spinorNorm (h2 : (2 : F) ≠ 0) (l : List (Fin n)) :
    spinorNorm (formD n F) polarD_nondegenerate h2 (signProductD l) =
      (Atlas.squareClass F (-1))^l.length := by
  induction l with
  | nil => simp [signProductD]
  | cons i l ih =>
    change spinorNorm (formD n F) polarD_nondegenerate h2 (signTorusD i * signProductD l) = _
    rw [map_mul, ih]
    have ht := hyperbolicTorus_spinorNorm (formD n F) polarD_nondegenerate h2
      (e i) (f i) (formD_e i) (formD_f i) (polarD_ef i) (-1) (neg_ne_zero.mpr one_ne_zero)
    have hu : Units.mk0 (-1 : F) (neg_ne_zero.mpr one_ne_zero) = (-1 : Fˣ) := Units.ext rfl
    rw [hu] at ht
    rw [signTorusD, ht, List.length_cons, pow_succ']

theorem negativeScalarD_spinorNorm (h2 : (2 : F) ≠ 0) :
    spinorNorm (formD n F) polarD_nondegenerate h2 (negativeScalarD n F) =
      Atlas.squareClass F ((-1 : Fˣ)^n) := by
  classical
  rw [negativeScalarD_eq_signProduct, signProductD_spinorNorm, Finset.length_toList,
    Finset.card_univ, Fintype.card_fin, map_pow]
theorem signProductD_determinant (l : List (Fin n)) :
    determinant (formD n F) (signProductD l) = 1 := by
  induction l with
  | nil => simp [signProductD]
  | cons i l ih =>
    change determinant (formD n F) (signTorusD i * signProductD l) = 1
    rw [map_mul, ih, mul_one]
    exact hyperbolicTorus_determinant _ _ _ _ _ _ _ _

theorem negativeScalarD_determinant : determinant (formD n F) (negativeScalarD n F) = 1 := by
  classical
  rw [negativeScalarD_eq_signProduct, signProductD_determinant]
end Atlas.Orthogonal


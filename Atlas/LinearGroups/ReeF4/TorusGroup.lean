import Atlas.LinearGroups.ReeF4.TorusDiagonal
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-! The actual faithful two-parameter subgroup of the 26-dimensional linear
automorphism group. Membership in the extra partial-product stabilizer is a
separate finite-field obligation. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def torusHom (m : ℕ) : Fˣ × Fˣ →* (TraceZero F ≃ₗ[F] TraceZero F) where
  toFun p := torusEquiv m p.1 p.2
  map_one' := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i j
      simp [torusEquiv, rootDiagonalEquiv, rootDiagonalLinear, rootDiagonalFormula]
  map_mul' p q := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i j
      simp [torusEquiv, rootDiagonalEquiv, rootDiagonalLinear, rootDiagonalFormula,
        torusWeight_mul, mul_assoc]

theorem torusHom_injective (m : ℕ) : Function.Injective (torusHom (F := F) m) := by
  intro p q h
  apply Prod.ext
  · apply Units.ext
    have hw := congrArg
      (fun g : TraceZero F ≃ₗ[F] TraceZero F => (g (rootVector (0,0))).val.2 0 0) h
    change (torusEquiv m p.1 p.2 (rootVector (0,0))).val.2 0 0 =
      (torusEquiv m q.1 q.2 (rootVector (0,0))).val.2 0 0 at hw
    rw [torusEquiv_root m p.1 p.2 (0,0), torusEquiv_root m q.1 q.2 (0,0)] at hw
    simpa [rootVector, Pi.single_apply, smul_eq_mul] using hw
  · apply Units.ext
    have hw := congrArg
      (fun g : TraceZero F ≃ₗ[F] TraceZero F => (g (rootVector (2,0))).val.2 2 0) h
    change (torusEquiv m p.1 p.2 (rootVector (2,0))).val.2 2 0 =
      (torusEquiv m q.1 q.2 (rootVector (2,0))).val.2 2 0 at hw
    rw [torusEquiv_root m p.1 p.2 (2,0), torusEquiv_root m q.1 q.2 (2,0)] at hw
    simpa [rootVector, Pi.single_apply, smul_eq_mul] using hw

def torusSubgroup (m : ℕ) : Subgroup (TraceZero F ≃ₗ[F] TraceZero F) :=
  (torusHom (F := F) m).range

def torusParameterEquiv (m : ℕ) : Fˣ × Fˣ ≃* torusSubgroup (F := F) m :=
  MulEquiv.ofBijective (torusHom m).rangeRestrict
    ⟨fun _ _ h => torusHom_injective m (congrArg Subtype.val h),
      (torusHom m).rangeRestrict_surjective⟩

theorem card_torusSubgroup {K : Type*} [Field K] [Finite K] [CharP K 2] (m : ℕ) :
    Nat.card (torusSubgroup (F := K) m) = (Nat.card K - 1)^2 := by
  rw [← Nat.card_congr (torusParameterEquiv (F := K) m).toEquiv, Nat.card_prod]
  simp [Nat.card_units, pow_two]

end Atlas.ReeF4


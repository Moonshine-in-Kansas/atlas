import Atlas.LinearGroups.ReeF4.WeylPermutation
import Atlas.LinearGroups.ReeF4.WeylOrder

/-! Coordinate transport by Weyl words, proved compositionally. -/
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F]

def weylCoordinateRead (w : TraceZero F) (c : WeylCoordinate) : F :=
  wilsonCoordinatesEquiv (w : Carrier F) c.1 c.2

def WeylCoordinateCompatible (e : TraceZero F ≃ₗ[F] TraceZero F)
    (p : Equiv.Perm WeylCoordinate) : Prop :=
  ∀ w c, weylCoordinateRead (e w) c = weylCoordinateRead w (p.symm c)

theorem weylCoordinateCompatible_mul
    {e f : TraceZero F ≃ₗ[F] TraceZero F} {p q : Equiv.Perm WeylCoordinate}
    (he : WeylCoordinateCompatible e p) (hf : WeylCoordinateCompatible f q) :
    WeylCoordinateCompatible (e * f) (p * q) := by
  intro w c
  change weylCoordinateRead (e (f w)) c = _
  rw [he, hf]
  rfl

theorem weylCoordinateCompatible_pow
    {e : TraceZero F ≃ₗ[F] TraceZero F} {p : Equiv.Perm WeylCoordinate}
    (he : WeylCoordinateCompatible e p) (n : ℕ) :
    WeylCoordinateCompatible (e ^ n) (p ^ n) := by
  induction n with
  | zero => intro w c; rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact weylCoordinateCompatible_mul ih he

theorem weylRho_coordinateCompatible :
    WeylCoordinateCompatible (weylRho (F := F)) weylRhoPermutation := by
  intro w c
  rcases c with ⟨i,j⟩
  change wilsonCoordinatesEquiv (weylRho w : Carrier F) i j = _
  rw [weylRho_coordinates]
  fin_cases i <;> fin_cases j <;> rfl

theorem weylSigma_coordinateCompatible :
    WeylCoordinateCompatible (weylSigma (F := F)) weylSigmaPermutation := by
  intro w c
  rcases c with ⟨i,j⟩
  change wilsonCoordinatesEquiv (weylSigma w : Carrier F) i j = _
  rw [weylSigma_coordinates]
  fin_cases i <;> fin_cases j <;> rfl

end Atlas.ReeF4

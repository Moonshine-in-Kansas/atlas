import Atlas.LinearGroups.ReeF4.WeylRootTransport
import Atlas.LinearGroups.ReeF4.TorusGroup

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def weylLongest : TraceZero F ≃ₗ[F] TraceZero F := (weylRho * weylSigma)^4

theorem weylLongest_coordinateCompatible :
    WeylCoordinateCompatible (weylLongest (F := F))
      ((weylRhoPermutation * weylSigmaPermutation)^4) :=
  weylCoordinateCompatible_pow
    (weylCoordinateCompatible_mul weylRho_coordinateCompatible
      weylSigma_coordinateCompatible) 4

set_option maxRecDepth 8192 in
theorem weylLongest_root_permutation : ∀ r : ShortRootLabel,
    ((weylRhoPermutation * weylSigmaPermutation)^4) (weylRootMark r) =
      weylRootMark (r.1, Fin.rev r.2) := by
  intro r
  rcases r with ⟨b,j⟩
  fin_cases b <;> fin_cases j <;> decide

theorem weylLongest_root (r : ShortRootLabel) :
    weylLongest (rootVector (F := F) r) = rootVector (r.1, Fin.rev r.2) :=
  weylCoordinateCompatible_root weylLongest_coordinateCompatible r _
    (weylLongest_root_permutation r)

set_option maxRecDepth 8192 in
theorem weylLongest_diagonal (i : Fin 3) :
    weylLongest (diagonalVector (F := F) i) = diagonalVector i := by
  apply Subtype.ext
  apply (wilsonCoordinatesEquiv (F := F)).injective
  funext j k
  change weylCoordinateRead (weylLongest (diagonalVector i)) (j,k) =
    weylCoordinateRead (diagonalVector i) (j,k)
  rw [weylLongest_coordinateCompatible (diagonalVector i) (j,k)]
  fin_cases j <;> fin_cases k <;> rfl

theorem weylLongest_square : (weylLongest (F := F))^2 = 1 := by
  simpa only [weylLongest, ← pow_mul] using weyl_product_pow_eight (F := F)

private theorem weylLongest_torus_intertwine (m : ℕ) (a b : Fˣ) :
    weylLongest * torusEquiv m a b = torusEquiv m a⁻¹ b⁻¹ * weylLongest := by
  apply LinearEquiv.toLinearMap_injective
  apply markedBasis.ext
  intro i
  rcases i with i | r
  · change weylLongest (torusEquiv m a b (markedBasis (.inl i))) =
      torusEquiv m a⁻¹ b⁻¹ (weylLongest (markedBasis (.inl i)))
    rw [markedBasis_diagonal, torusEquiv_diagonal, weylLongest_diagonal,
      torusEquiv_diagonal]
  · change weylLongest (torusEquiv m a b (markedBasis (.inr r))) =
      torusEquiv m a⁻¹ b⁻¹ (weylLongest (markedBasis (.inr r)))
    rw [markedBasis_root, torusEquiv_root, map_smul, weylLongest_root,
      torusEquiv_root, torusWeight_opposite]
    simp [torusWeight, mul_comm]

/-- The actual longest relative Weyl element inverts both torus parameters. -/
theorem weylLongest_torus (m : ℕ) (a b : Fˣ) :
    weylLongest * torusEquiv m a b * weylLongest⁻¹ = torusEquiv m a⁻¹ b⁻¹ := by
  rw [weylLongest_torus_intertwine, mul_assoc, mul_inv_cancel, mul_one]

/-- Inversion is an equality in the ambient linear automorphism group. -/
theorem weylLongest_torus_inverse (m : ℕ) (a b : Fˣ) :
    weylLongest * torusEquiv m a b * weylLongest⁻¹ = (torusEquiv m a b)⁻¹ := by
  rw [weylLongest_torus]
  exact map_inv (torusHom (F := F) m) (a,b)

end Atlas.ReeF4

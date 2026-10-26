import Atlas.LinearGroups.ReeF4.WeylTorusWeights
import Atlas.LinearGroups.ReeF4.WeylSupport
import Atlas.LinearGroups.ReeF4.TorusGroup

namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem weylOperator_root (g : Fin 2) (r : ShortRootLabel) :
    weylOperator (F := F) g (rootVector r) = rootVector (weylRootImage g r) := by
  simpa [weylSupport, starMarkedVector] using weylOperator_support (F := F) g (.inr r)

private theorem weylOperator_square (g : Fin 2) :
    weylOperator (F := F) g * weylOperator g = 1 := by
  fin_cases g
  · change weylRho * weylRho = (1 : TraceZero F ≃ₗ[F] TraceZero F)
    simpa only [pow_two] using weylRho_square (F := F)
  · change weylSigma * weylSigma = (1 : TraceZero F ≃ₗ[F] TraceZero F)
    simpa only [pow_two] using weylSigma_square (F := F)

private theorem weyl_torus_intertwine (m : ℕ) (g : Fin 2) (a b c d : Fˣ)
    (hw : ∀ r, torusWeight m a b (weylRootImage g r) = torusWeight m c d r) :
    torusEquiv m a b * weylOperator g = weylOperator g * torusEquiv m c d := by
  apply LinearEquiv.toLinearMap_injective
  apply markedBasis.ext
  intro i
  rcases i with i | r
  · change torusEquiv m a b (weylOperator g (markedBasis (.inl i))) =
      weylOperator g (torusEquiv m c d (markedBasis (.inl i)))
    rw [markedBasis_diagonal, torusEquiv_diagonal]
    have hi := weylOperator_support (F := F) g (.inl i)
    change weylOperator g (diagonalVector (Fin.castLE (by decide) i)) = _ at hi
    simp only [hi]
    fin_cases g <;> fin_cases i <;>
      simp [weylSupport, starMarkedVector, _root_.map_add]
  · change torusEquiv m a b (weylOperator g (markedBasis (.inr r))) =
      weylOperator g (torusEquiv m c d (markedBasis (.inr r)))
    rw [markedBasis_root, weylOperator_root, torusEquiv_root, torusEquiv_root,
      map_smul, weylOperator_root, hw]

private theorem weyl_torus_conjugate (m : ℕ) (g : Fin 2) (a b c d : Fˣ)
    (hw : ∀ r, torusWeight m a b (weylRootImage g r) = torusWeight m c d r) :
    weylOperator g * torusEquiv m a b * weylOperator g = torusEquiv m c d := by
  rw [mul_assoc, weyl_torus_intertwine m g a b c d hw,
    ← mul_assoc, weylOperator_square, one_mul]

theorem weylSigma_torus (m : ℕ) (a b : Fˣ) :
    weylSigma * torusEquiv m a b * weylSigma = torusEquiv m b a :=
  weyl_torus_conjugate m 1 a b b a (torusWeight_sigma m a b)

theorem weylRho_torus {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (a b : Fˣ) :
    weylRho * torusEquiv m a b * weylRho =
      torusEquiv m a (thetaUnits m a * b⁻¹) :=
  weyl_torus_conjugate m 0 a b a (thetaUnits m a * b⁻¹) (torusWeight_rho hcard a b)

end Atlas.ReeF4

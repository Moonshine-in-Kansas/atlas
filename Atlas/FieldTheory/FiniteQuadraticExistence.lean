import Atlas.FieldTheory.FiniteQuadraticExtension
import Mathlib.FieldTheory.Finite.GaloisField

/-! Actual finite quadratic extensions for numerical prime-power parameters.
The fields are the existing mathlib splitting-field constructions; an algebra
embedding is supplied by finite-field extension divisibility. -/
noncomputable section
namespace Atlas.FiniteQuadratic

/-- The actual splitting fields of degrees f and 2f admit a quadratic tower. -/
theorem galoisField_quadratic_algebra (p f : ℕ) [Fact p.Prime] (hf : 0 < f) :
    ∃ (_ : Algebra (GaloisField p f) (GaloisField p (2*f))),
      Module.finrank (GaloisField p f) (GaloisField p (2*f)) = 2 := by
  have hf0 : f ≠ 0 := by omega
  have h2f : 2*f ≠ 0 := by omega
  have hdiv : Module.finrank (ZMod p) (GaloisField p f) ∣
      Module.finrank (ZMod p) (GaloisField p (2*f)) := by
    rw [GaloisField.finrank p hf0, GaloisField.finrank p h2f]
    exact dvd_mul_left f 2
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdiv
  algebraize [e.toRingHom]
  refine ⟨inferInstance, ?_⟩
  have ht := Module.finrank_mul_finrank (ZMod p) (GaloisField p f) (GaloisField p (2*f))
  rw [GaloisField.finrank p hf0, GaloisField.finrank p h2f] at ht
  nlinarith

/-- Every positive prime power is realized as the base field of an actual
quadratic finite-field extension, with no group-theoretic assumptions. -/
theorem exists_prime_power_quadratic (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) :
    ∃ (F K : Type) (_ : Field F) (_ : Field K) (_ : Finite F) (_ : Finite K)
      (_ : Algebra F K), Nat.card F = p^f ∧ Module.finrank F K = 2 ∧
        Nat.card K = p^(2*f) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,ha⟩ := galoisField_quadratic_algebra p f (by omega)
  let := a
  exact ⟨GaloisField p f, GaloisField p (2*f), inferInstance, inferInstance,
    inferInstance, inferInstance, a, GaloisField.card p f (by omega), ha,
      GaloisField.card p (2*f) (by omega)⟩
end Atlas.FiniteQuadratic

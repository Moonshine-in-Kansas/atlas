import Atlas.LinearGroups.Triality.Torus

/-! Scalar intersection of the actual torus, independent of group order.
Confining an arbitrary scalar in the generated group to this torus remains
part of the Bruhat/action-kernel argument. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem torus_scalar_eq_one (h : Kˣ × Fˣ) (c : K) (hc : c^2 = 1)
    (hs : ∀ x : VectorD 4 K, (torusMap F K h).val x = c • x) : c = 1 := by
  have h0 := congrFun (hs (e (0 : Fin 4))) (.inl 0)
  have h1 := congrFun (hs (e (1 : Fin 4))) (.inl 1)
  have h2 := congrFun (hs (e (2 : Fin 4))) (.inl 2)
  simp [torusMap, torusWeights, diagonalEmbedding, diagonalLinear, sigmaUnit,
    baseUnit, e, Pi.smul_apply, smul_eq_mul] at h0 h1 h2
  rcases sq_eq_one_iff.mp hc with hc | hc
  · exact hc
  have hb : algebraMap F K (h.2 : F) = 1 := by
    rw [h0, hc] at h1
    have hh := (div_eq_iff (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))).mp h1
    simpa only [neg_mul_neg, one_mul] using hh
  have hh : (1 : K) = -1 := by
    simpa [h0, hc, hb] using h2
  exact hc.trans hh.symm

theorem torus_scalar_trivial (h : Kˣ × Fˣ) (c : K) (hc : c^2 = 1)
    (hs : ∀ x : VectorD 4 K, (torusMap F K h).val x = c • x) :
    torusMap F K h = 1 := by
  have hc1 := torus_scalar_eq_one F K h c hc hs
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  simpa [hc1] using hs x

end Atlas.Triality

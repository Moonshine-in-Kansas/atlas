import Atlas.Algebra.Albert.CubicPolarization

/-! Recover the projected cross product from the actual quadratic and cubic
forms. This implication uses polarization only in the forward direction. -/
namespace Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

theorem traceZeroPolar_of_quadratic (g : TraceZero F ≃ₗ[F] TraceZero F)
    (hq : ∀ w, traceZeroQuadratic (g w) = traceZeroQuadratic w)
    (u v : TraceZero F) : traceZeroPolar (g u) (g v) = traceZeroPolar u v := by
  rw [traceZeroPolar_quadratic, ← map_add, hq, hq, hq,
    ← traceZeroPolar_quadratic]

theorem traceZeroCross_of_forms (g : TraceZero F ≃ₗ[F] TraceZero F)
    (hq : ∀ w, traceZeroQuadratic (g w) = traceZeroQuadratic w)
    (hc : ∀ w, traceZeroCubic (g w) = traceZeroCubic w)
    (u v : TraceZero F) : traceZeroCross (g u) (g v) = g (traceZeroCross u v) := by
  apply sub_eq_zero.mp
  apply traceZeroPolar_nondegenerate
  intro z
  obtain ⟨w, rfl⟩ := g.surjective z
  have hp : traceZeroPolar (traceZeroCross (g u) (g v)) (g w) =
      traceZeroPolar (traceZeroCross u v) w := by
    rw [← traceZeroCubic_fullPolarization, ← traceZeroCubic_fullPolarization]
    simp only [← map_add, hc]
  rw [sub_eq_add_neg, traceZeroPolar_add_left, ← neg_one_smul F,
    traceZeroPolar_smul_left, traceZeroPolar_of_quadratic g hq, hp]
  ring

end Atlas.Albert

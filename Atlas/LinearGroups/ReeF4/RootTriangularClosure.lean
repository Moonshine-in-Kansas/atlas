import Atlas.LinearGroups.ReeF4.RootTriangularData

namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F]

/-- Actual coordinate unitriangularity, allowing the three scalar coordinates
of degree zero to remain redundant on the trace kernel. -/
def AbsoluteUnitriangular (e : TraceZero F ≃ₗ[F] TraceZero F) : Prop :=
  ∀ w c, (∀ d, absoluteCoordinateGrade c < absoluteCoordinateGrade d →
    weylCoordinateRead w d = 0) → weylCoordinateRead (e w) c = weylCoordinateRead w c

theorem absoluteUnitriangular_one : AbsoluteUnitriangular (1 : TraceZero F ≃ₗ[F] TraceZero F) := by
  intro w c h
  rfl

theorem absoluteUnitriangular_mul {e f : TraceZero F ≃ₗ[F] TraceZero F}
    (he : AbsoluteUnitriangular e) (hf : AbsoluteUnitriangular f) :
    AbsoluteUnitriangular (e * f) := by
  intro w c hzero
  change weylCoordinateRead (e (f w)) c = _
  have hfw : ∀ d, absoluteCoordinateGrade c < absoluteCoordinateGrade d →
      weylCoordinateRead (f w) d = 0 := by
    intro d hd
    rw [hf w d (by intro t ht; exact hzero t (lt_trans hd ht))]
    exact hzero d hd
  rw [he (f w) c hfw, hf w c hzero]

/-- A Weyl prefix transports a finite support certificate into the actual
unitriangular linear group. The only formula assumption is the explicit
underlying action of f; no membership or group-order assumption enters. -/
theorem absoluteUnitriangular_conj_of_formula
    {e f : TraceZero F ≃ₗ[F] TraceZero F} {p : Equiv.Perm WeylCoordinate}
    (he : WeylCoordinateCompatible e p) (formula : Carrier F → Carrier F)
    (hformula : ∀ w : TraceZero F, (f w : Carrier F) = formula (w : Carrier F))
    (hsupport : StrictlyLoweringFormula p formula) :
    AbsoluteUnitriangular (e * f * e⁻¹) := by
  have hinv (w : TraceZero F) (d : WeylCoordinate) :
      weylCoordinateRead (e⁻¹ w) d = weylCoordinateRead w (p d) := by
    have h := he (e⁻¹ w) (p d)
    simpa using h.symm
  intro w c hzero
  change weylCoordinateRead (e (f (e⁻¹ w))) c = _
  rw [he (f (e⁻¹ w)) c]
  have h := hsupport (e⁻¹ w : TraceZero F).val (p.symm c) (by
    intro d hd
    change weylCoordinateRead (e⁻¹ w) d = 0
    rw [hinv]
    apply hzero
    simpa using hd)
  change wilsonCoordinatesEquiv (f (e⁻¹ w) : Carrier F) (p.symm c).1
    (p.symm c).2 = _
  rw [hformula, h]
  change weylCoordinateRead (e⁻¹ w) (p.symm c) = _
  rw [hinv]
  simp

end Atlas.ReeF4

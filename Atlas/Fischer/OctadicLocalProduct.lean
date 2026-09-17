import Atlas.Fischer.OctadicRootMapOctad
import Atlas.Fischer.OctadHyperplaneLocalConvolution

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable
local instance (O : Octad) : Fintype (OctadShortenedHyperplane O) := Subtype.fintype _

private theorem sum_fintype_irrel {α M : Type*} [AddCommMonoid M]
    (h₁ h₂ : Fintype α) (f : α → M) :
    (∑ x ∈ @Finset.univ α h₁, f x) = ∑ x ∈ @Finset.univ α h₂, f x := by
  have h : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

/-- The fixed-hyperplane convolution uses its actual shortened-code sum map. -/
theorem calibratedHyperplaneConvolution_local {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    (∑ c : OctadShortenedHyperplane O, calibratedHyperplaneConvolutionTerm Q (b, c)) =
      (1 / 2 : Scalar) • (octadicHyperplanePart Q 0 - calibratedHyperplaneVector Q b -
        calibratedHyperplaneVector Q (octadHyperplaneComplement O b)) := by
  have hs : (∑ c : OctadHyperplaneLocalDomain O b,
      (1 / 2 : Scalar) • calibratedHyperplaneVector Q (octadHyperplaneLocalSum O b c)) =
      ∑ c : OctadShortenedHyperplane O, calibratedHyperplaneConvolutionTerm Q (b, c) := by
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro c hc
      have hn : ¬ (b.val + c.val ≠ 0 ∧ b.val + c.val ≠ octadShortenedOne O) := by
        intro h
        exact hc ⟨⟨c, h⟩, rfl⟩
      simp [calibratedHyperplaneConvolutionTerm, hn]
    · intro c
      simp [calibratedHyperplaneConvolutionTerm, c.property, octadHyperplaneLocalSum]
  rw [← hs, ← Finset.smul_sum]
  congr 1
  have hl := octadHyperplane_local_convolution O b (calibratedHyperplaneVector Q)
  rw [octadicHyperplanePart_zero]
  convert hl using 1
  · exact sum_fintype_irrel _ _ _
  · exact congrArg (fun z : Coordinates => z - calibratedHyperplaneVector Q b -
      calibratedHyperplaneVector Q (octadHyperplaneComplement O b)) (sum_fintype_irrel _ _ _)

/-- Product with the full hyperplane sum, including diagonal and complement terms. -/
theorem product_calibratedHyperplane_hyperplanePart {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    product (calibratedHyperplaneVector Q b) (octadicHyperplanePart Q 0) =
      product (calibratedHyperplaneVector Q b) (calibratedHyperplaneVector Q b) +
      (theta / 2) • signedOctadVector Q.octadLift +
      (1 / 2 : Scalar) • (octadicHyperplanePart Q 0 - calibratedHyperplaneVector Q b -
        calibratedHyperplaneVector Q (octadHyperplaneComplement O b)) := by
  conv_lhs => rhs; rw [octadicHyperplanePart_zero]
  rw [product_sum_right, Finset.sum_congr rfl (fun c _ =>
    product_calibratedHyperplanes_partition Q b c)]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [calibratedHyperplaneConvolution_local]

end Atlas.Fischer

import Atlas.Fischer.OctadicDiagonalSum
import Atlas.Fischer.OctadicComplementProducts
import Atlas.Fischer.OctadHyperplaneConvolution

set_option backward.isDefEq.respectTransparency false

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

private theorem shortened_twice (O : Octad) (b : octadShortenedCode O) : b + b = 0 := by
  rw [← two_smul Bit, show (2 : Bit) = 0 from rfl, zero_smul]

private theorem hyperplane_sum_zero_iff (O : Octad) (b c : OctadShortenedHyperplane O) :
    b.val + c.val = 0 ↔ b = c := by
  constructor
  · intro h
    apply Subtype.ext
    have hh := congrArg (fun z : octadShortenedCode O => z + c.val) h
    simpa only [add_assoc, shortened_twice, add_zero, zero_add] using hh
  · intro h
    rw [h]
    exact shortened_twice O _

private theorem hyperplane_sum_one_iff (O : Octad) (b c : OctadShortenedHyperplane O) :
    b.val + c.val = octadShortenedOne O ↔ c = octadHyperplaneComplement O b := by
  constructor
  · intro h
    apply Subtype.ext
    have hh := congrArg (fun z : octadShortenedCode O => b.val + z) h
    simpa only [← add_assoc, shortened_twice, zero_add, octadHyperplaneComplement] using hh
  · rintro rfl
    change b.val + (b.val + octadShortenedOne O) = octadShortenedOne O
    rw [← add_assoc, shortened_twice, zero_add]

def calibratedHyperplaneConvolutionTerm {O : Octad} (Q : OctadCalibration O)
    (p : OctadShortenedHyperplane O × OctadShortenedHyperplane O) : Coordinates :=
  if h : p.1.val + p.2.val ≠ 0 ∧ p.1.val + p.2.val ≠ octadShortenedOne O then
    (1 / 2 : Scalar) • calibratedHyperplaneVector Q ⟨p.1.val + p.2.val, h⟩ else 0

theorem product_calibratedHyperplanes_partition {O : Octad} (Q : OctadCalibration O)
    (b c : OctadShortenedHyperplane O) :
    product (calibratedHyperplaneVector Q b) (calibratedHyperplaneVector Q c) =
      (if b = c then product (calibratedHyperplaneVector Q b) (calibratedHyperplaneVector Q b) else 0) +
      (if c = octadHyperplaneComplement O b then (theta / 2) • signedOctadVector Q.octadLift else 0) +
      calibratedHyperplaneConvolutionTerm Q (b, c) := by
  classical
  by_cases hbc : b = c
  · subst c
    have hn := Ne.symm (octadHyperplaneComplement_ne O b)
    simp [calibratedHyperplaneConvolutionTerm, shortened_twice, hn]
  · by_cases hc : c = octadHyperplaneComplement O b
    · have hs := (hyperplane_sum_one_iff O b c).mpr hc
      have hp := product_calibrated_hyperplanes_complement Q b c hs
      have hn : ¬ (b.val + c.val ≠ 0 ∧ b.val + c.val ≠ octadShortenedOne O) :=
        fun h => h.2 hs
      simp only [ite_eq_right hbc, ite_eq_left hc, calibratedHyperplaneConvolutionTerm,
        dif_neg hn, zero_add, add_zero]
      calc
        _ = (1 / 2 : Scalar) • ((2 : Scalar) • product
          (calibratedHyperplaneVector Q b) (calibratedHyperplaneVector Q c)) := by
          rw [smul_smul]; norm_num
        _ = _ := by rw [hp, smul_smul]; congr 1; ring
    · have hs : b.val + c.val ≠ 0 ∧ b.val + c.val ≠ octadShortenedOne O :=
        ⟨fun h => hbc ((hyperplane_sum_zero_iff O b c).mp h),
          fun h => hc ((hyperplane_sum_one_iff O b c).mp h)⟩
      have hp := product_calibrated_hyperplanes_four Q b c ⟨b.val + c.val, hs⟩ rfl
      simp only [ite_eq_right hbc, ite_eq_right hc, calibratedHyperplaneConvolutionTerm, dif_pos hs,
        zero_add]
      rw [← hp, smul_smul]
      norm_num

theorem calibratedHyperplaneConvolution_sum {O : Octad} (Q : OctadCalibration O) :
    (∑ p : OctadShortenedHyperplane O × OctadShortenedHyperplane O,
      calibratedHyperplaneConvolutionTerm Q p) = (14 : Scalar) • octadicHyperplanePart Q 0 := by
  classical
  have hs : (∑ p : OctadHyperplaneSumPair O,
      (1 / 2 : Scalar) • calibratedHyperplaneVector Q (octadHyperplaneSum O p)) =
      ∑ p : OctadShortenedHyperplane O × OctadShortenedHyperplane O,
        calibratedHyperplaneConvolutionTerm Q p := by
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro p hp
      have hn : ¬ (p.1.val + p.2.val ≠ 0 ∧ p.1.val + p.2.val ≠ octadShortenedOne O) := by
        intro h
        exact hp ⟨⟨p, h⟩, rfl⟩
      simp [calibratedHyperplaneConvolutionTerm, hn]
    · intro p
      simp [calibratedHyperplaneConvolutionTerm, p.property, octadHyperplaneSum]
  rw [← hs]
  have hc : (∑ p : OctadHyperplaneSumPair O,
      (1 / 2 : Scalar) • calibratedHyperplaneVector Q (octadHyperplaneSum O p)) =
      28 • ∑ b : OctadShortenedHyperplane O, (1 / 2 : Scalar) • calibratedHyperplaneVector Q b := by
    convert octadHyperplane_convolution O
      (fun b => (1 / 2 : Scalar) • calibratedHyperplaneVector Q b) using 1
    · exact sum_fintype_irrel _ _ _
    · exact congrArg (fun x : Coordinates => (28 : ℕ) • x) (sum_fintype_irrel _ _ _)
  rw [hc, ← Finset.smul_sum, ← octadicHyperplanePart_zero]
  module

/-- Sixth row of the source square table, derived from actual Parker products
and actual shortened-code fibers, rather than a coefficient certificate. -/
theorem product_octadicHyperplanePart_self {O : Octad} (Q : OctadCalibration O) :
    product (octadicHyperplanePart Q 0) (octadicHyperplanePart Q 0) =
      (-15 : Scalar) • octadAxisSum O + (15 : Scalar) • octadExteriorAxisSum O +
      (15 * theta) • signedOctadVector Q.octadLift + (14 : Scalar) • octadicHyperplanePart Q 0 := by
  rw [octadicHyperplanePart_zero, product_sum_left]
  simp only [product_sum_right]
  rw [Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ =>
    product_calibratedHyperplanes_partition Q b c))]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [calibratedHyperplane_diagonal_sum, Finset.sum_const, Finset.card_univ,
    octadShortenedHyperplane_card, ← Fintype.sum_prod_type, calibratedHyperplaneConvolution_sum]
  rw [octadicHyperplanePart_zero]
  module

end Atlas.Fischer

import Atlas.Fischer.OctadicMixedAxisProducts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem calibratedHyperplaneSupport_mem {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) (i : Omega) :
    i ∈ (signedOctadSupport (calibratedHyperplaneLift Q b)).val ↔ b.val.val.val i = 1 := by
  change i ∈ support b.val.val.val ↔ _
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  have hb : ∀ t : Bit, t ≠ 0 ↔ t = 1 := by decide
  exact hb _

theorem product_calibratedHyperplane_self {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    product (calibratedHyperplaneVector Q b) (calibratedHyperplaneVector Q b) =
      octadBasisProduct (signedOctadSupport (calibratedHyperplaneLift Q b))
        (signedOctadSupport (calibratedHyperplaneLift Q b)) := by
  simp only [calibratedHyperplaneVector, signedOctadVector, product_smul_left,
    product_smul_right, parkerScalarSign_star, smul_smul, parkerScalarSign_square,
    one_smul, product_xOctad]

/-- The thirty actual diagonal terms in Y², using the verified fifteen
hyperplanes through each exterior point. -/
theorem calibratedHyperplane_diagonal_sum {O : Octad} (Q : OctadCalibration O) :
    (∑ b : OctadShortenedHyperplane O,
      product (calibratedHyperplaneVector Q b) (calibratedHyperplaneVector Q b)) =
      (-15 : Scalar) • octadAxisSum O + (15 : Scalar) • octadExteriorAxisSum O := by
  classical
  funext k
  cases k with
  | inr D =>
    simp only [Finset.sum_apply, product_calibratedHyperplane_self, octadBasisProduct,
      ite_true, Pi.smul_apply, Pi.sub_apply, Pi.add_apply]
    simp [octadAxisSum, octadExteriorAxisSum, Finset.sum_apply]
  | inl i =>
    simp only [Finset.sum_apply, product_calibratedHyperplane_self,
      octadBasisProduct_axis_apply, ite_true, calibratedHyperplaneSupport_mem]
    by_cases hi : i ∈ O.val
    · have hz (b : OctadShortenedHyperplane O) : b.val.val.val i = 0 :=
        (mem_octadShortenedCode O b.val.val).mp b.val.property i hi
      simp only [hz, zero_ne_one, ite_false, Finset.sum_const, Finset.card_univ,
        octadShortenedHyperplane_card]
      norm_num [octadAxisSum, octadExteriorAxisSum, Finset.sum_apply, hi]
    · have hc : Fintype.card {b : OctadShortenedHyperplane O // b.val.val.val i = 1} = 15 :=
        octadShortenedHyperplane_through_point O ⟨i, hi⟩
      have hf : (Finset.univ.filter (fun b : OctadShortenedHyperplane O => b.val.val.val i = 1)).card = 15 :=
        (Fintype.card_subtype _).symm.trans hc
      have ht (b : OctadShortenedHyperplane O) :
          (if b.val.val.val i = 1 then (3 / 2 : Scalar) else -1 / 2) =
            (if b.val.val.val i = 1 then (2 : Scalar) else 0) - 1 / 2 := by
        split_ifs <;> ring
      simp only [ht, Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero,
        add_zero, Finset.sum_const, Finset.card_univ, octadShortenedHyperplane_card, hf]
      norm_num [octadAxisSum, octadExteriorAxisSum, Finset.sum_apply, hi]

end Atlas.Fischer

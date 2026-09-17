import Atlas.Fischer.ProductTable

namespace Atlas.Fischer
open Atlas.Codes

@[simp] theorem u_axis_apply (i j : Omega) : u i (Sum.inl j) = if j = i then 1 else 0 := by
  classical
  simp [u, coordinateVector, Pi.single_apply]

@[simp] theorem u_octad_apply (i : Omega) (O : Octad) : u i (Sum.inr O) = 0 := by
  classical
  simp [u, coordinateVector, Pi.single_apply]

@[simp] theorem xOctad_axis_apply (O : Octad) (i : Omega) : xOctad O (Sum.inl i) = 0 := by
  classical
  simp [xOctad, coordinateVector, Pi.single_apply]

@[simp] theorem xOctad_octad_apply (O P : Octad) :
    xOctad O (Sum.inr P) = if P = O then 1 else 0 := by
  classical
  simp [xOctad, coordinateVector, Pi.single_apply]

theorem hermitian_coordinateVector_left (i : CoordinateIndex) (y : Coordinates) :
    hermitian (coordinateVector i) y = (coordinateWeight i : Scalar) * star (y i) := by
  classical
  simp only [hermitian, weightedHermitian, coordinateVector, Pi.single_apply,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem octadWord_injective : Function.Injective octadWord := by
  intro O P h
  apply Subtype.ext
  rw [← octadWord_support O, ← octadWord_support P, h]

theorem octadWord_signedSupport (d : SignedOctad) :
    octadWord (signedOctadSupport d) = d.val.1 := by
  apply Subtype.ext
  apply support_injective
  exact octadWord_support (signedOctadSupport d)

theorem signedOctadSupport_eq_iff (d : SignedOctad) (O : Octad) :
    signedOctadSupport d = O ↔ d.val.1 = octadWord O := by
  rw [← octadWord_signedSupport d, octadWord_injective.eq_iff]

theorem signedOctadVector_octad_apply (d : SignedOctad) (O : Octad) :
    signedOctadVector d (Sum.inr O) =
      if octadWord O = d.val.1 then parkerScalarSign d.val.2 else 0 := by
  classical
  have he : O = signedOctadSupport d ↔ octadWord O = d.val.1 := by
    rw [← octadWord_signedSupport d, octadWord_injective.eq_iff]
  simp [signedOctadVector, he]

@[simp] theorem signedOctadVector_axis_apply (d : SignedOctad) (i : Omega) :
    signedOctadVector d (Sum.inl i) = 0 := by simp [signedOctadVector]

theorem octadWord_intersection (O P : Octad) :
    signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) =
      overlap (octadWord O : BinaryWord) (octadWord P : BinaryWord) :=
  signedOctadIntersection_overlap _ _

theorem octadWord_sum_weight (A B C : Octad)
    (h : octadWord A = octadWord B + octadWord C) :
    signedOctadIntersection (canonicalOctadLift B) (canonicalOctadLift C) = 4 := by
  have hw := binary_weight_add (octadWord B : BinaryWord) (octadWord C : BinaryWord)
  have ha : hammingNorm ((octadWord B : BinaryWord) + (octadWord C : BinaryWord)) = 8 := by
    rw [← Submodule.coe_add, ← h, octadWord_weight]
  rw [ha, octadWord_weight, octadWord_weight] at hw
  rw [octadWord_intersection]
  omega

theorem octadWord_complementary_sum_weight (A B C : Octad)
    (h : octadWord A = octadWord B + octadWord C + golayOne) :
    signedOctadIntersection (canonicalOctadLift B) (canonicalOctadLift C) = 0 := by
  have hw := binary_weight_add (octadWord B : BinaryWord) (octadWord C : BinaryWord)
  have hc := complement_weight ((octadWord B : BinaryWord) + (octadWord C : BinaryWord))
  have ha : hammingNorm (((octadWord B : BinaryWord) + (octadWord C : BinaryWord)) + allOnes) = 8 := by
    change hammingNorm ((octadWord B + octadWord C + golayOne : golay) : BinaryWord) = 8
    rw [← h, octadWord_weight]
  rw [ha] at hc
  rw [octadWord_weight, octadWord_weight] at hw
  rw [octadWord_intersection]
  omega

end Atlas.Fischer

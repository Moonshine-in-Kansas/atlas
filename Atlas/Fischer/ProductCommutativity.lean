import Atlas.Fischer.CoordinateProduct
import Atlas.Fischer.ParkerLoopIdentities

namespace Atlas.Fischer
open Atlas.Codes

theorem signedOctadIntersection_symm (d f : SignedOctad) :
    signedOctadIntersection d f = signedOctadIntersection f d := by
  simp [signedOctadIntersection, Finset.inter_comm]

theorem parker_octad_commutes (d f : SignedOctad)
    (h : signedOctadIntersection d f = 0 ∨ signedOctadIntersection d f = 4) :
    parkerLoopMultiply d.val f.val = parkerLoopMultiply f.val d.val := by
  have hz : golayHalfOverlap d.val.1 f.val.1 = 0 := by
    unfold golayHalfOverlap
    rw [← signedOctadIntersection_overlap]
    rcases h with h | h <;> rw [h] <;> rfl
  rw [parkerLoopMultiply_commutator, hz, parkerSign_zero]

theorem octadProductFour_swap (d f : SignedOctad)
    (h : signedOctadIntersection d f = 4) (h' : signedOctadIntersection f d = 4) :
    octadProductFour d f h = octadProductFour f d h' := by
  apply Subtype.ext
  exact parker_octad_commutes d f (Or.inr h)

theorem octadProductDisjoint_swap (d f : SignedOctad)
    (h : signedOctadIntersection d f = 0) (h' : signedOctadIntersection f d = 0) :
    octadProductDisjoint d f h = octadProductDisjoint f d h' := by
  apply Subtype.ext
  exact congrArg (fun z => parkerLoopMultiply z (golayOne, 0))
    (parker_octad_commutes d f (Or.inl h))

theorem axisBasisProduct_comm (i j : Omega) : axisBasisProduct i j = axisBasisProduct j i := by
  classical
  by_cases h : i = j
  · subst j; rfl
  · simp only [axisBasisProduct, if_neg h, if_neg (Ne.symm h)]
    congr 1
    rw [add_comm ((15 : Scalar) • u i)]
    congr 1
    congr 1
    ext k
    simp [and_comm]

theorem octadBasisProduct_comm (O P : Octad) : octadBasisProduct O P = octadBasisProduct P O := by
  classical
  by_cases he : O = P
  · subst P; rfl
  have hi := signedOctadIntersection_symm (canonicalOctadLift O) (canonicalOctadLift P)
  unfold octadBasisProduct
  rw [if_neg he, if_neg (Ne.symm he)]
  by_cases h4 : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 4
  · have h4' : signedOctadIntersection (canonicalOctadLift P) (canonicalOctadLift O) = 4 := hi ▸ h4
    rw [dif_pos h4, dif_pos h4', octadProductFour_swap _ _ h4 h4']
  · have h4' : ¬signedOctadIntersection (canonicalOctadLift P) (canonicalOctadLift O) = 4 := hi ▸ h4
    rw [dif_neg h4, dif_neg h4']
    by_cases h0 : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 0
    · have h0' : signedOctadIntersection (canonicalOctadLift P) (canonicalOctadLift O) = 0 := hi ▸ h0
      rw [dif_pos h0, dif_pos h0', octadProductDisjoint_swap _ _ h0 h0']
    · have h0' : ¬signedOctadIntersection (canonicalOctadLift P) (canonicalOctadLift O) = 0 := hi ▸ h0
      rw [dif_neg h0, dif_neg h0']

theorem basisProduct_comm (i j : CoordinateIndex) : basisProduct i j = basisProduct j i := by
  cases i with
  | inl i => cases j with
    | inl j => exact axisBasisProduct_comm i j
    | inr O => rfl
  | inr O => cases j with
    | inl i => rfl
    | inr P => exact octadBasisProduct_comm O P

theorem product_comm (x y : Coordinates) : product x y = product y x := by
  unfold product
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [basisProduct_comm, mul_comm]

end Atlas.Fischer

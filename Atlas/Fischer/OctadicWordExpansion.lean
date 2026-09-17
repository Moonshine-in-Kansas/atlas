import Atlas.Fischer.GolayCoordinateVectors
import Atlas.Fischer.ProductMaps

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The zero word, the complement word and the30 hyperplanes are precisely the
32 words of the actual shortened octad code. -/
def octadicWordIndexEquiv (O : Octad) :
    Unit ⊕ (Unit ⊕ OctadShortenedHyperplane O) ≃ octadShortenedCode O where
  toFun i := match i with
    | .inl _ => 0
    | .inr (.inl _) => octadShortenedOne O
    | .inr (.inr b) => b.val
  invFun b := if h0 : b=0 then .inl () else
    if hX : b=octadShortenedOne O then .inr (.inl ()) else .inr (.inr ⟨b,h0,hX⟩)
  left_inv i := by
    rcases i with u | (u | b)
    · cases u
      simp
    · cases u
      simp [octadShortenedOne_ne_zero]
    · simp [b.property.1,b.property.2]
  right_inv b := by
    dsimp only
    split_ifs <;> simp_all

/-- The zero component carries the actual U-part; the other31 components are
exactly the calibrated signed octad vectors, with θ on the complement word. -/
def octadicWordTerm {O : Octad} (Q : OctadCalibration O)
    (b : octadShortenedCode O) : Coordinates :=
  match (octadicWordIndexEquiv O).symm b with
  | .inl _ => octadicAxisPart O
  | .inr (.inl _) => theta • signedOctadVector Q.octadLift
  | .inr (.inr a) => calibratedHyperplaneVector Q a

theorem octadicWordTerm_index {O : Octad} (Q : OctadCalibration O)
    (i : Unit ⊕ (Unit ⊕ OctadShortenedHyperplane O)) :
    octadicWordTerm Q (octadicWordIndexEquiv O i)=match i with
      | .inl _ => octadicAxisPart O
      | .inr (.inl _) => theta • signedOctadVector Q.octadLift
      | .inr (.inr a) => calibratedHyperplaneVector Q a := by
  unfold octadicWordTerm
  rw [Equiv.symm_apply_apply]

/-- The literal octadic formula reindexed by all actual shortened words. -/
theorem octadicRoot_word_expansion {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) :
    octadicRoot Q χ=(1/2 : Scalar) •
      ∑ b : octadShortenedCode O, parkerScalarSign (χ b) • octadicWordTerm Q b := by
  rw [← Equiv.sum_comp (octadicWordIndexEquiv O)]
  simp only [octadicWordTerm_index,Fintype.sum_sum_type,Fintype.sum_unique]
  change octadicRoot Q χ=(1/2 : Scalar) •
    (parkerScalarSign (χ 0) • octadicAxisPart O+
      (parkerScalarSign (χ (octadShortenedOne O)) • (theta • signedOctadVector Q.octadLift)+
        ∑ b : OctadShortenedHyperplane O, parkerScalarSign (χ b.val) • calibratedHyperplaneVector Q b))
  rw [map_zero,show parkerScalarSign 0=1 from rfl,one_smul]
  unfold octadicRoot
  congr 1
  rw [smul_smul,mul_comm (parkerScalarSign _) theta]
  exact add_assoc _ _ _

/-- Exact bilinear product expansion before any coordinate magnitudes or
signs are inferred. It retains every one of the32×32 actual word pairs. -/
theorem product_octadicRoot_word_expansion {F G : Octad}
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (χ : OctadicCharacter F) (ψ : OctadicCharacter G) :
    product (octadicRoot Q χ) (octadicRoot R ψ)=(1/4 : Scalar) •
      ∑ b : octadShortenedCode F, ∑ c : octadShortenedCode G,
        (parkerScalarSign (χ b)*parkerScalarSign (ψ c)) •
          product (octadicWordTerm Q b) (octadicWordTerm R c) := by
  rw [octadicRoot_word_expansion Q,octadicRoot_word_expansion R,
    product_smul_left,product_smul_right]
  simp only [product_sum_left,product_sum_right,product_smul_left,product_smul_right,
    parkerScalarSign_star,Finset.smul_sum,smul_smul]
  norm_num only [star_div₀,star_one,star_ofNat]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  ring

end Atlas.Fischer

import Atlas.Fischer.OctadicCharacterAverage
import Atlas.Fischer.OctadicOrthogonality

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
local instance octadicDisjointCharacterFinite (O : Octad) : Finite (OctadicCharacter O) := Nat.finite_of_card_ne_zero (by rw [octadCharacters_card]; decide)
local instance octadicDisjointCharacterFintype (O : Octad) : Fintype (OctadicCharacter O) := Fintype.ofFinite _

/-- Point-axis pairing of two disjoint actual Golay octads. -/
theorem octadicAxisPart_disjoint_pairing (O F : Octad)
    (hOF : Disjoint O.val F.val) :
    hermitian (octadicAxisPart O) (octadicAxisPart F) = -1 := by
  classical
  unfold hermitian weightedHermitian
  rw [Fintype.sum_sum_type]
  have hz (D : Octad) : octadicAxisPart O (.inr D) = 0 := by
    simp [octadicAxisPart, u, coordinateVector]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  have hi (i : Omega) : (coordinateWeight (.inl i) : Scalar) *
      octadicAxisPart O (.inl i) * star (octadicAxisPart F (.inl i)) =
      (1/8 : Scalar) - (if i ∈ O.val then 1/4 else 0) -
        (if i ∈ F.val then 1/4 else 0) := by
    rw [octadicAxisPart_axis_apply, octadicAxisPart_axis_apply]
    have hn : ¬ (i ∈ O.val ∧ i ∈ F.val) := fun h =>
      Finset.disjoint_left.mp hOF h.1 h.2
    by_cases hO : i ∈ O.val <;> by_cases hF : i ∈ F.val <;>
      norm_num [coordinateWeight, hO, hF] at *
  rw [Finset.sum_congr rfl (fun i _ => hi i)]
  simp only [Finset.sum_sub_distrib]
  have hs (A : Finset Omega) (a : Scalar) :
      (∑ i : Omega, if i ∈ A then a else 0) = (A.card : Scalar) * a := by
    rw [← Finset.sum_filter]
    simp
  rw [hs, hs, octad_size O.val O.property, octad_size F.val F.property]
  have hc : Fintype.card Omega = 24 := by decide
  norm_num [hc]

/-- The source average is exactly minus one quarter: the unnormalized sum
of all 32 by 32 pairings is minus256. -/
theorem octadicRoot_disjoint_pairing_sum (O F : Octad)
    (hOF : Disjoint O.val F.val) (Q : OctadCalibration O) (R : OctadCalibration F) :
    (∑ χ : OctadicCharacter O, ∑ ψ : OctadicCharacter F,
      hermitian (octadicRoot Q χ) (octadicRoot R ψ)) = -256 := by
  simp_rw [← hermitian_sum_right]
  rw [← hermitian_sum_left]
  rw [octadicRoot_character_sum, octadicRoot_character_sum,
    hermitian_smul_left, hermitian_smul_right, octadicAxisPart_disjoint_pairing O F hOF]
  norm_num

end Atlas.Fischer

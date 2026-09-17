import Atlas.Fischer.OctadicDisjointAverage
import Atlas.Fischer.BasicOctadicRays
import Atlas.Fischer.OctadicReflectingRoots
import Atlas.Fischer.ReflectingRootPairing

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
local instance octadicNonrealCharacterFintype (O : Octad) : Fintype (OctadicCharacter O) := Fintype.ofFinite _

/-- For every two disjoint octads, some actual calibrated character roots have
nonreal Hermitian pairing. This is forced by their negative character average. -/
theorem octadicRoot_disjoint_exists_nonreal (O F : Octad)
    (hOF : Disjoint O.val F.val) (Q : OctadCalibration O) (R : OctadCalibration F) :
    ∃ χ : OctadicCharacter O, ∃ ψ : OctadicCharacter F,
      star (hermitian (octadicRoot Q χ) (octadicRoot R ψ)) ≠
        hermitian (octadicRoot Q χ) (octadicRoot R ψ) := by
  classical
  by_contra hn
  push_neg at hn
  have hne : O ≠ F := by
    intro h
    subst F
    have he : O.val = ∅ := disjoint_self.mp hOF
    have hc := octad_size O.val O.property
    rw [he] at hc
    simp at hc
  have hp (χ : OctadicCharacter O) (ψ : OctadicCharacter F) :
      hermitian (octadicRoot Q χ) (octadicRoot R ψ) = 0 ∨
        hermitian (octadicRoot Q χ) (octadicRoot R ψ) = 1 := by
    have hd : ¬ ∃ a : Scalar, a^3=1 ∧ octadicRoot R ψ = a • octadicRoot Q χ := by
      intro h
      have he := (rootRay_eq_iff _ _).mpr h
      exact hne (octadic_ray_eq_implies_octad_eq R Q ψ χ he).symm
    have hs := reflectingRoot_pairing_square _ _
      (octadicRoot_isReflectingRoot Q χ) (octadicRoot_isReflectingRoot R ψ) hd
    rw [hn χ ψ] at hs
    have hz : hermitian (octadicRoot Q χ) (octadicRoot R ψ) *
        (hermitian (octadicRoot Q χ) (octadicRoot R ψ) - 1) = 0 := by
      linear_combination hs
    exact (mul_eq_zero.mp hz).imp id sub_eq_zero.mp
  have hpos : 0 ≤ (scalarToComplex (∑ χ : OctadicCharacter O, ∑ ψ : OctadicCharacter F,
      hermitian (octadicRoot Q χ) (octadicRoot R ψ))).re := by
    simp only [map_sum, Complex.re_sum]
    apply Finset.sum_nonneg
    intro χ _
    apply Finset.sum_nonneg
    intro ψ _
    rcases hp χ ψ with h | h <;> rw [h] <;> norm_num
  rw [octadicRoot_disjoint_pairing_sum O F hOF Q R] at hpos
  norm_num [map_ofNat] at hpos

end Atlas.Fischer

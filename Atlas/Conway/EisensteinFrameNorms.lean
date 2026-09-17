import Atlas.Conway.EisensteinFrameOrder

namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators QuadraticAlgebra

theorem eisensteinRationalUnit_norm (u : Eisensteinˣ) :
    star (eisensteinToRational (u : Eisenstein))*eisensteinToRational (u : Eisenstein) = 1 := by
  rcases (eisenstein_norm_one_iff (u : Eisenstein)).mp
    ((eisenstein_isUnit_iff (u : Eisenstein)).mp u.isUnit) with h|h|h|h|h|h
  all_goals rw [h]; decide +kernel

theorem eisensteinFrameVector_hermitian (p : Fin 12 × Eisensteinˣ) :
    eisensteinHermitian (eisensteinFrameVector p) (eisensteinFrameVector p) = 6 := by
  have hsum : (∑ i, star (eisensteinFrameVector p i)*eisensteinFrameVector p i) =
      star (eisensteinFrameScale*eisensteinToRational (p.2 : Eisenstein))*
        (eisensteinFrameScale*eisensteinToRational (p.2 : Eisenstein)) := by
    simp [eisensteinFrameVector,Pi.single_apply,mul_ite,ite_mul]
  unfold eisensteinHermitian
  rw [hsum,star_mul]
  have he : star (eisensteinToRational (p.2 : Eisenstein)) * star eisensteinFrameScale *
      (eisensteinFrameScale*eisensteinToRational (p.2 : Eisenstein)) =
      (star eisensteinFrameScale*eisensteinFrameScale)*
        (star (eisensteinToRational (p.2 : Eisenstein))*eisensteinToRational (p.2 : Eisenstein)) := by ring
  rw [he,eisensteinRationalUnit_norm,mul_one]
  decide +kernel

theorem eisensteinCoordinateFrame_norm_six (z : EisensteinRationalCoordinates)
    (hz : z ∈ eisensteinCoordinateFrame) : eisensteinBilinear z z = 6 := by
  obtain ⟨p,rfl⟩ := hz
  unfold eisensteinBilinear
  rw [eisensteinFrameVector_hermitian]
  norm_num [eisensteinReal]

end Atlas.Conway

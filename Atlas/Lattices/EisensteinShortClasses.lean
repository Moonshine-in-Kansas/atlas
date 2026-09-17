import Atlas.Lattices.EisensteinShells
import Atlas.Lattices.EisensteinRank
import Atlas.Lattices.EisensteinShortGeometry
import Atlas.Lattices.EisensteinRotationLattice

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators QuadraticAlgebra

abbrev EisensteinClasses := EisensteinLattice ⧸ eisensteinThetaEnd.range

def eisensteinClass : EisensteinLattice →ₗ[ℤ] EisensteinClasses :=
  eisensteinThetaEnd.range.mkQ

theorem eisensteinClasses_card : Nat.card EisensteinClasses = 531441 := by
  exact eisensteinTheta_quotient_card

theorem eisensteinNorm_theta (z : EisensteinLattice) :
    eisensteinNorm (eisensteinTheta • z) = 3*eisensteinNorm z := by
  unfold eisensteinNorm
  rw [eisensteinBilinear_self, eisensteinBilinear_self]
  have he (i : Fin 12) :
      ((eisensteinCoordinateEmbedding (eisensteinTheta • z).val i).re^2 -
       (eisensteinCoordinateEmbedding (eisensteinTheta • z).val i).re *
         (eisensteinCoordinateEmbedding (eisensteinTheta • z).val i).im +
       (eisensteinCoordinateEmbedding (eisensteinTheta • z).val i).im^2) =
      3*((eisensteinCoordinateEmbedding z.val i).re^2 -
       (eisensteinCoordinateEmbedding z.val i).re * (eisensteinCoordinateEmbedding z.val i).im +
       (eisensteinCoordinateEmbedding z.val i).im^2) := by
    simp [eisensteinCoordinateEmbedding, eisensteinToRational, eisensteinTheta,
      eisensteinOmega, QuadraticAlgebra.omega]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  ring

theorem eisensteinNorm_theta_minimum (z : EisensteinLattice)
    (hz : z ∈ eisensteinThetaEnd.range) (hne : z≠0) : 12 ≤ eisensteinNorm z := by
  obtain ⟨w, rfl⟩ := hz
  have hw : w ≠ 0 := fun h => hne (by rw [h, map_zero])
  change 12 ≤ eisensteinNorm (eisensteinTheta • w)
  rw [eisensteinNorm_theta]
  linarith [eisensteinNorm_minimum w hw]

def eisensteinLatticeRotation (z : EisensteinLattice) : EisensteinLattice :=
  eisensteinOmega • z

theorem eisensteinLatticeRotation_class (z : EisensteinLattice) :
    eisensteinClass (eisensteinLatticeRotation z) = eisensteinClass z := by
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨(1+eisensteinOmega) • z, ?_⟩
  apply Subtype.ext
  funext i
  change eisensteinTheta * ((1+eisensteinOmega)*z.val i) =
    eisensteinOmega*z.val i-z.val i
  have h : eisensteinTheta*(1+eisensteinOmega) = eisensteinOmega-1 := by
    ext <;> norm_num [eisensteinTheta, eisensteinOmega, QuadraticAlgebra.omega]
  rw [← mul_assoc, h]
  ring

end Atlas.Lattices

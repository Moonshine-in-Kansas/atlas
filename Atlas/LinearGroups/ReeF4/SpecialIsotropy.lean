import Atlas.LinearGroups.ReeF4.SpecialIsotropyFormulas
import Atlas.LinearGroups.ReeF4.SpecialIsotropyIdentity
import Atlas.LinearGroups.ReeF4.SpecialVectors
import Atlas.LinearGroups.ReeF4.StarCoefficientChecks

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
theorem rawStar_quadratic_zero (u v : TraceZero F) (h : StarDomain u v) :
    traceZeroQuadratic (proposedStarLinear (wedge u v))=0 := by
  rw [isotropyQuadratic_actual,isotropyRawStar_actual,isotropy_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [← isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [← isotropyPolar_actual,h.1]
  simp [isotropyCertificate,hc,hp]

theorem proposedPartialProduct_quadratic_zero (σ : F →+* F)
    (u v : TraceZero F) (h : StarDomain u v) :
    traceZeroQuadratic (proposedPartialProduct σ u v h)=0 := by
  change quadraticTrace (Atlas.Albert.map σ (proposedStarLinear (wedge u v)).val)=0
  rw [quadraticTrace_map]
  change σ (traceZeroQuadratic (proposedStarLinear (wedge u v)))=0
  rw [rawStar_quadratic_zero u v h,σ.map_zero]

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
theorem IsSpecialVector.quadratic_zero {m : ℕ} {u : TraceZero K}
    (hu : IsSpecialVector m u) : traceZeroQuadratic u=0 := by
  obtain ⟨_,v,h,he⟩ := hu
  calc
    traceZeroQuadratic u = traceZeroQuadratic
        (proposedPartialProduct (thetaInv K m).toRingHom u v h) :=
      congrArg traceZeroQuadratic he
    _ = 0 := proposedPartialProduct_quadratic_zero (thetaInv K m).toRingHom u v h
end FiniteField
end Atlas.ReeF4

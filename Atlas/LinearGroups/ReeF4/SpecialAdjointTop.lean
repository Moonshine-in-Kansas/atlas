import Atlas.LinearGroups.ReeF4.SpecialAdjointTopIdentity9
import Atlas.LinearGroups.ReeF4.SpecialAdjointTopIdentity17
import Atlas.LinearGroups.ReeF4.SpecialVectors

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
theorem rawStar_specialAdjoint9_zero (u v : TraceZero F) (h : StarDomain u v) :
    specialAdjoint9 (isotropyCoordinates (proposedStarLinear (wedge u v))) = 0 := by
  rw [isotropyRawStar_actual,specialAdjoint9_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [specialAdjoint9Certificate,hc,hp]

theorem proposedPartialProduct_specialAdjoint9_zero (σ : F →+* F)
    (u v : TraceZero F) (h : StarDomain u v) :
    specialAdjoint9 (isotropyCoordinates (proposedPartialProduct σ u v h)) = 0 := by
  change specialAdjoint9 (isotropyCoordinates
    (traceZeroMap σ (proposedStarLinear (wedge u v)))) = 0
  rw [isotropyCoordinates_map,specialAdjoint9_map,rawStar_specialAdjoint9_zero u v h,σ.map_zero]
theorem rawStar_specialAdjoint17_zero (u v : TraceZero F) (h : StarDomain u v) :
    specialAdjoint17 (isotropyCoordinates (proposedStarLinear (wedge u v))) = 0 := by
  rw [isotropyRawStar_actual,specialAdjoint17_quartic_identity]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,h.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,h.1]
  simp [specialAdjoint17Certificate,hc,hp]

theorem proposedPartialProduct_specialAdjoint17_zero (σ : F →+* F)
    (u v : TraceZero F) (h : StarDomain u v) :
    specialAdjoint17 (isotropyCoordinates (proposedPartialProduct σ u v h)) = 0 := by
  change specialAdjoint17 (isotropyCoordinates
    (traceZeroMap σ (proposedStarLinear (wedge u v)))) = 0
  rw [isotropyCoordinates_map,specialAdjoint17_map,rawStar_specialAdjoint17_zero u v h,σ.map_zero]

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
theorem IsSpecialVector.specialAdjoint9_zero {m : ℕ} {u : TraceZero K}
    (hu : IsSpecialVector m u) : specialAdjoint9 (isotropyCoordinates u) = 0 := by
  obtain ⟨_,v,h,he⟩ := hu
  calc
    specialAdjoint9 (isotropyCoordinates u) = specialAdjoint9
      (isotropyCoordinates (proposedPartialProduct (thetaInv K m).toRingHom u v h)) :=
      congrArg (fun w => specialAdjoint9 (isotropyCoordinates w)) he
    _ = 0 := proposedPartialProduct_specialAdjoint9_zero _ u v h

theorem IsSpecialVector.adjoint_coordinate9_zero {m : ℕ} {u : TraceZero K}
    (hu : IsSpecialVector m u) : (adjoint u.val).2 0 7 = 0 := by
  rw [specialAdjoint9_actual]
  exact hu.specialAdjoint9_zero
theorem IsSpecialVector.specialAdjoint17_zero {m : ℕ} {u : TraceZero K}
    (hu : IsSpecialVector m u) : specialAdjoint17 (isotropyCoordinates u) = 0 := by
  obtain ⟨_,v,h,he⟩ := hu
  calc
    specialAdjoint17 (isotropyCoordinates u) = specialAdjoint17
      (isotropyCoordinates (proposedPartialProduct (thetaInv K m).toRingHom u v h)) :=
      congrArg (fun w => specialAdjoint17 (isotropyCoordinates w)) he
    _ = 0 := proposedPartialProduct_specialAdjoint17_zero _ u v h

theorem IsSpecialVector.adjoint_coordinate17_zero {m : ℕ} {u : TraceZero K}
    (hu : IsSpecialVector m u) : (adjoint u.val).2 1 7 = 0 := by
  rw [specialAdjoint17_actual]
  exact hu.specialAdjoint17_zero
end FiniteField
end Atlas.ReeF4

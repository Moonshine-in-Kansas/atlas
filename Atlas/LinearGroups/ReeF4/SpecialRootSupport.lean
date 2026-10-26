import Atlas.LinearGroups.ReeF4.SpecialIsotropyFormulas
import Atlas.LinearGroups.ReeF4.SpecialVectors

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

private theorem isotropyCoordinates_injective :
    Function.Injective (isotropyCoordinates (F := F)) := by
  intro u v h
  calc
    u = isotropyPoint (isotropyCoordinates u) := (isotropyPoint_coordinates u).symm
    _ = isotropyPoint (isotropyCoordinates v) := congrArg isotropyPoint h
    _ = v := isotropyPoint_coordinates v

/-- No isotropy premise is used: on the full prescribed domain, a diagonal-only
left argument has zero star image. -/
theorem rawStar_zero_of_root_coordinates_zero (u v : TraceZero F)
    (hu : ∀ b j, u.val.2 b j = 0) (h : StarDomain u v) :
    proposedStarLinear (wedge u v) = 0 := by
  have hp : u.val.1 1 * v.val.1 0 + u.val.1 0 * v.val.1 1 = 0 := by
    have hp := h.1
    rw [isotropyPolar_actual] at hp
    simpa [isotropyPolar,isotropyCoordinates,hu] using hp
  have hr : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) = 0 := by
    funext k
    fin_cases k <;> simp [isotropyRawStar,isotropyCoordinates,hu,hp]
  apply isotropyCoordinates_injective
  rw [isotropyRawStar_actual,hr,_root_.map_zero]

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- Every special vector has genuine root support; it cannot be supported only
on the two marked diagonal coordinates. No cardinality hypothesis is needed. -/
theorem IsSpecialVector.exists_root_coordinate_ne_zero {m : ℕ} {u : TraceZero K}
    (hu : IsSpecialVector m u) : ∃ b j, u.val.2 b j ≠ 0 := by
  classical
  by_contra hn
  have hz : ∀ b j, u.val.2 b j = 0 := by
    simpa only [not_exists,not_not] using hn
  obtain ⟨hu,v,hd,he⟩ := hu
  apply hu
  change u = traceZeroMap (thetaInv K m).toRingHom
    (proposedStarLinear (wedge u v)) at he
  rw [rawStar_zero_of_root_coordinates_zero u v hz hd,traceZeroMap_zero] at he
  exact he
end FiniteField
end Atlas.ReeF4

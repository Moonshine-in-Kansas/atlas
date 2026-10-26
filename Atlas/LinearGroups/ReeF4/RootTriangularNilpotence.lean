import Atlas.LinearAlgebra.CoordinateLoweringNilpotence
import Atlas.LinearGroups.ReeF4.RootTriangularClosure

/-! Filtration nilpotence and finite-subgroup consequences, independent of target orders. -/
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F]

def weylCoordinateReadLinear : TraceZero F →ₗ[F] (WeylCoordinate → F) where
  toFun w := weylCoordinateRead w
  map_add' u v := by
    funext c
    exact congrFun (congrFun ((wilsonCoordinatesEquiv (F := F)).map_add u.val v.val) c.1) c.2
  map_smul' a v := by
    funext c
    exact congrFun (congrFun ((wilsonCoordinatesEquiv (F := F)).map_smul a v.val) c.1) c.2

theorem weylCoordinateReadLinear_injective :
    Function.Injective (weylCoordinateReadLinear (F := F)) := by
  intro u v h
  apply Subtype.ext
  apply (wilsonCoordinatesEquiv (F := F)).injective
  funext b j
  exact congrFun h (b,j)

theorem absoluteCoordinateGrade_bounds (c : WeylCoordinate) :
    -12 ≤ absoluteCoordinateGrade c ∧ absoluteCoordinateGrade c ≤ 12 := by
  rcases c with ⟨b,j⟩
  fin_cases b <;> fin_cases j <;> decide

theorem AbsoluteUnitriangular.sub_one_pow_twentyFive
    {e : TraceZero F ≃ₗ[F] TraceZero F} (he : AbsoluteUnitriangular e) :
    (e.toLinearMap - 1) ^ 25 = 0 := by
  apply Atlas.LinearAlgebra.coordinate_lowering_pow_eq_zero
    (weylCoordinateReadLinear (F := F)) (weylCoordinateReadLinear_injective (F := F))
    absoluteCoordinateGrade (-12) 12
    (fun c => (absoluteCoordinateGrade_bounds c).1)
    (fun c => (absoluteCoordinateGrade_bounds c).2)
    e.toLinearMap he 25
  norm_num

variable [CharP F 2]

/-- Explicit local characteristic instance, avoiding any extra field or
nontriviality assumption on the public exponent theorem. -/
private theorem traceZeroEnd_charTwo : CharP (Module.End F (TraceZero F)) 2 := by
  letI : Nontrivial F := CharP.nontrivial_of_char_ne_one (R := F) (by decide : 2 ≠ 1)
  letI : Nontrivial (TraceZero F) :=
    (traceZeroCoordinateEquiv (F := F)).toEquiv.nontrivial
  have htwo : (2 : Module.End F (TraceZero F)) = 0 := by
    have h := congrArg (algebraMap F (Module.End F (TraceZero F)))
      (CharTwo.two_eq_zero (R := F))
    simpa only [map_ofNat, map_zero] using h
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero htwo

-- The endomorphism-to-automorphism comparison needs extra elaboration budget.
set_option maxHeartbeats 1000000 in
theorem AbsoluteUnitriangular.pow_thirtyTwo
    {e : TraceZero F ≃ₗ[F] TraceZero F} (he : AbsoluteUnitriangular e) : e ^ 32 = 1 := by
  letI : CharP (Module.End F (TraceZero F)) 2 := traceZeroEnd_charTwo
  have hp := Atlas.LinearAlgebra.pow_thirtyTwo_eq_one_of_sub_one_pow_twentyFive_eq_zero
    e.toLinearMap he.sub_one_pow_twentyFive
  let f : (TraceZero F ≃ₗ[F] TraceZero F) →* Module.End F (TraceZero F) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hf : Function.Injective f := by
    intro a b h
    exact LinearEquiv.toLinearMap_injective h
  apply hf
  rw [map_pow, map_one]
  exact hp

theorem isPGroup_of_absoluteUnitriangular
    (H : Subgroup (TraceZero F ≃ₗ[F] TraceZero F))
    (hH : ∀ e ∈ H, AbsoluteUnitriangular e) : IsPGroup 2 H := by
  apply Atlas.LinearAlgebra.isPGroup_two_of_pow_thirtyTwo
  intro e
  apply Subtype.ext
  exact (hH e.val e.property).pow_thirtyTwo

theorem nilpotent_of_absoluteUnitriangular
    (H : Subgroup (TraceZero F ≃ₗ[F] TraceZero F)) [Finite H]
    (hH : ∀ e ∈ H, AbsoluteUnitriangular e) : Group.IsNilpotent H :=
  (isPGroup_of_absoluteUnitriangular H hH).isNilpotent

theorem solvable_of_absoluteUnitriangular
    (H : Subgroup (TraceZero F ≃ₗ[F] TraceZero F)) [Finite H]
    (hH : ∀ e ∈ H, AbsoluteUnitriangular e) : Group.IsSolvable H := by
  letI := nilpotent_of_absoluteUnitriangular H hH
  infer_instance

end Atlas.ReeF4

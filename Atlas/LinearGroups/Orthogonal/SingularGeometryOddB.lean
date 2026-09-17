import Atlas.LinearGroups.Orthogonal.SingularPrimitiveB2

/-! # Uniform odd-characteristic singular-line geometry from rank two -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F]

theorem singularPointsB_primitive_rank_two_up (n : ℕ) (h2 : (2 : F) ≠ 0) :
    MulAction.IsPreprimitive (elementarySubgroup (formB (n+2) F))
      (SingularPoints (formB (n+2) F)) := by
  cases n with
  | zero => exact singularPointsB2_primitive h2
  | succ n => exact singularPointsB_primitive n h2

theorem projectiveSingularB_primitive_rank_two_up (n : ℕ) (h2 : (2 : F) ≠ 0) :
    MulAction.IsPreprimitive (ProjectiveElementary (formB (n+2) F))
      (SingularPoints (formB (n+2) F)) := by
  letI := singularPointsB_primitive_rank_two_up (F := F) n h2
  let f : SingularPoints (formB (n+2) F) →ₑ[projectiveElementaryMap (formB (n+2) F)]
      SingularPoints (formB (n+2) F) :=
    { toFun := id, map_smul' := fun _ _ => rfl }
  exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id

theorem singular_stabilizerB_perpendicular_transitive_rank_two_up (n : ℕ) (h2 : (2 : F) ≠ 0)
    (p r s : SingularPoints (formB (n+2) F)) (hr : r ≠ p) (hs : s ≠ p)
    (hpr : SingularPerp (formB (n+2) F) p r)
    (hps : SingularPerp (formB (n+2) F) p s) :
    ∃g : MulAction.stabilizer (elementarySubgroup (formB (n+2) F)) p,g • r=s := by
  cases n with
  | zero => exact singular_stabilizerB2_perpendicular_transitive h2 p r s hr hs hpr hps
  | succ n => exact singular_stabilizerB_perpendicular_transitive n h2 p r s hr hs hpr hps

end Atlas.Orthogonal

import Atlas.FieldTheory.FiniteQuadraticCounts

/-! # Fibres of the quadratic norm on the entire field -/
noncomputable section
namespace Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem norm_fiber_zero_card (hdeg : Module.finrank F K = 2) :
    Nat.card {x : K // norm F K x = 0} = 1 := by
  let e : {x : K // norm F K x = 0} ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨0, by simp⟩
    left_inv := fun x => Subtype.ext ((norm_zero_iff hdeg x.val).mp x.prop).symm
    right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (by simp)

theorem norm_fiber_card (hdeg : Module.finrank F K = 2) (a : F) (ha : a ≠ 0) :
    Nat.card {x : K // norm F K x = a} = Nat.card F + 1 := by
  let au : Fˣ := Units.mk0 a ha
  let e : {x : K // norm F K x = a} ≃
      {x : Kˣ // Units.map (norm F K) x = au} := {
    toFun := fun x => ⟨Units.mk0 x.val (by
      intro hx
      apply ha
      exact x.prop.symm.trans ((norm_zero_iff hdeg x.val).mpr hx)), by
      apply Units.ext
      exact x.prop⟩
    invFun := fun x => ⟨x.val.val, by
      have h := congrArg Units.val x.prop
      exact h⟩
    left_inv := fun _ => rfl
    right_inv := fun x => Subtype.ext (Units.ext rfl) }
  exact (Nat.card_congr e).trans (norm_units_fiber_card hdeg au)

end Atlas.FiniteQuadratic

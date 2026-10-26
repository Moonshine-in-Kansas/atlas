import Atlas.LinearGroups.F4.NearPointGeometry
import Atlas.LinearGroups.Orthogonal.SingularCount

/-! Independent counts for the near rank-one cone, before orbit identification. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

def NonzeroNearSpin := {v : Fin 8 → F // v ≠ 0 ∧ nearQuadratic v = 0}

def nonzeroNearSpinEquiv : NonzeroNearSpin (F:=F) ≃ Atlas.Orthogonal.NonzeroSingularD 4 F where
  toFun v := ⟨⟨nearHyperbolicEquiv v.val, by
    rw [← nearQuadratic_hyperbolic]
    exact v.prop.2⟩, by
    intro h
    exact v.prop.1 (nearHyperbolicEquiv.injective (h.trans (map_zero _).symm))⟩
  invFun v := ⟨nearHyperbolicEquiv.symm v.val.val, by
    constructor
    · intro h
      exact v.prop (nearHyperbolicEquiv.symm.injective (h.trans (map_zero _).symm))
    · rw [nearQuadratic_hyperbolic, LinearEquiv.apply_symm_apply]
      exact v.val.prop⟩
  left_inv v := Subtype.ext (nearHyperbolicEquiv.symm_apply_apply _)
  right_inv v := Subtype.ext (Subtype.ext (nearHyperbolicEquiv.apply_symm_apply _))

/-- Actual rank-one vectors in the marked nine-space, outside its marked line. -/
def NearVectors := {x : Atlas.Albert.Carrier F //
  x ∈ parabolicImageZero ∧ nearSpinCoordinates x ≠ 0 ∧ Atlas.Albert.adjoint x = 0}

def nearVectorsEquiv : NearVectors (F:=F) ≃ F × NonzeroNearSpin (F:=F) where
  toFun x := (x.val.2 2 0, ⟨nearSpinCoordinates x.val, x.prop.2.1,
    (imageZero_rankOne_iff x.val x.prop.1).mp x.prop.2.2⟩)
  invFun w := ⟨nearVector w.1 w.2.val, nearVector_mem_imageZero _ _, by
    rw [nearVector_spin]
    exact w.2.prop.1, (nearVector_rankOne_iff _ _).mpr w.2.prop.2⟩
  left_inv x := Subtype.ext (nearVector_reconstruction x.val x.prop.1)
  right_inv w := by
    apply Prod.ext
    · exact nearVector_C0 _ _
    · exact Subtype.ext (nearVector_spin _ _)

theorem card_nonzeroNearSpin [Finite F] :
    Nat.card (NonzeroNearSpin (F:=F)) = (Nat.card F ^ 4 - 1) * (Nat.card F ^ 3 + 1) := by
  rw [Nat.card_congr nonzeroNearSpinEquiv, Atlas.Orthogonal.card_nonzero_singularD]

theorem card_nearVectors [Finite F] :
    Nat.card (NearVectors (F:=F)) =
      Nat.card F * ((Nat.card F ^ 4 - 1) * (Nat.card F ^ 3 + 1)) := by
  rw [Nat.card_congr nearVectorsEquiv, Nat.card_prod, card_nonzeroNearSpin]

end Atlas.F4

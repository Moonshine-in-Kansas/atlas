import Atlas.LinearGroups.Symplectic.Isometry

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

/-- Quadratic refinements specified by their zero value and exact polar form. -/
abbrev FormRefinement (n : ℕ) (F : Type*) [Field F] :=
  {Q : Vector n F → F // Q 0=0 ∧ ∀ x y,Q (x+y)=Q x+Q y+form x y}

instance formRefinementAction : MulAction (Sp n F) (FormRefinement n F) where
  smul g Q := ⟨fun x => Q.val (toLinear (n := n) (F := F) g⁻¹ x),by
    change Q.val (toLinear g⁻¹ 0)=0
    rw [map_zero,Q.prop.1],by
    intro x y
    change Q.val (toLinear g⁻¹ (x+y))=Q.val (toLinear g⁻¹ x)+Q.val (toLinear g⁻¹ y)+form x y
    rw [map_add,Q.prop.2]
    have h := preserves g⁻¹ x y
    change form (toLinear g⁻¹ x) (toLinear g⁻¹ y)=form x y at h
    rw [h]⟩
  one_smul Q := by
    apply Subtype.ext
    funext x
    change Q.val ((1 : Sp n F)⁻¹ • x)=Q.val x
    simp
  mul_smul g h Q := by
    apply Subtype.ext
    funext x
    change Q.val ((g*h)⁻¹ • x)=Q.val (h⁻¹ • (g⁻¹ • x))
    rw [mul_inv_rev,mul_smul]

@[simp] theorem formRefinementAction_apply (g : Sp n F) (Q : FormRefinement n F) (x : Vector n F) :
    (g • Q).val x=Q.val (g⁻¹ • x) := rfl

theorem formRefinement_zeroCount_invariant (g : Sp n F) (Q : FormRefinement n F) :
    Nat.card {x : Vector n F // (g • Q).val x=0} = Nat.card {x : Vector n F // Q.val x=0} := by
  exact Nat.card_congr (Equiv.subtypeEquiv (toLinear g⁻¹).toEquiv (fun _ => Iff.rfl))

end Atlas.Symplectic

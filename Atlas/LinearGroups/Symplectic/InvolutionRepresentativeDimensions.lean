import Atlas.LinearGroups.Symplectic.InvolutionRepresentatives
import Atlas.LinearAlgebra.AlternatingFinrank

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]
open Atlas.LinearInvolution

abbrev signSupport (S : Finset (Fin n)) := {i : Index n // Sum.elim id id i ∈ S}

private def signSupportEquiv (S : Finset (Fin n)) : signSupport S ≃ (S ⊕ S) where
  toFun x := match x with
    | ⟨.inl i,hi⟩ => .inl ⟨i,hi⟩
    | ⟨.inr i,hi⟩ => .inr ⟨i,hi⟩
  invFun x := match x with
    | .inl ⟨i,hi⟩ => ⟨.inl i,hi⟩
    | .inr ⟨i,hi⟩ => ⟨.inr i,hi⟩
  left_inv x := by rcases x with ⟨i,hi⟩; cases i <;> rfl
  right_inv x := by cases x <;> rfl

def signMinusEquiv (S : Finset (Fin n)) (h2 : (2 : F) ≠ 0) :
    minus (toLinear (signRepresentative S : Sp n F)).toLinearMap ≃ₗ[F] (signSupport S → F) where
  toFun x i := x.val i.val
  invFun y := ⟨fun i => if hi : Sum.elim id id i ∈ S then y ⟨i,hi⟩ else 0, by
    rw [mem_minus]
    funext i
    change ((signRepresentative S : Sp n F) • (fun j => if hj : Sum.elim id id j ∈ S then y ⟨j,hj⟩ else 0)) i = _
    rw [signRepresentative_apply]
    by_cases hi : Sum.elim id id i ∈ S <;> simp [hi]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : Sum.elim id id i ∈ S
    · simp [hi]
    · simp only [hi,↓reduceDIte]
      have hx := congrFun ((mem_minus _ _).mp x.prop) i
      change ((signRepresentative S : Sp n F) • x.val) i = -x.val i at hx
      rw [signRepresentative_apply,if_neg hi,one_mul] at hx
      have hh : (2 : F) * x.val i = 0 := by linear_combination hx
      exact ((mul_eq_zero.mp hh).resolve_left h2).symm
  right_inv x := by funext i; simp only [dif_pos i.prop]
  map_add' x y := rfl
  map_smul' c x := rfl

theorem signRepresentative_minusDimension (S : Finset (Fin n)) (h2 : (2 : F) ≠ 0) :
    minusDimension (signRepresentative S : Sp n F) = 2*S.card := by
  classical
  unfold minusDimension
  rw [(signMinusEquiv S h2).finrank_eq,Module.finrank_pi]
  have hc := Fintype.card_congr (signSupportEquiv S)
  simpa [Fintype.card_sum,Fintype.card_coe,mul_two,two_mul] using hc

theorem square_one_minusDimension_even (g : Sp n F) (hg : g^2=1) (h2 : (2:F) ≠ 0) :
    Even (minusDimension g) := by
  have ht : Function.Involutive (toLinear g).toLinearMap := by
    intro x
    change g • (g • x) = x
    rw [←mul_smul,←pow_two,hg,one_smul]
  apply Atlas.AlternatingForm.even_finrank
    (form.restrict (minus (toLinear g).toLinearMap))
  · intro x; exact form_self x.val
  · exact minus_nondegenerate (form (n := n) (F := F)) form_nondegenerate (toLinear g).toLinearMap ht (preserves g) h2

end Atlas.Symplectic

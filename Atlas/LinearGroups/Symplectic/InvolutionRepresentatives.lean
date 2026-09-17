import Atlas.LinearGroups.Symplectic.InvolutionConjugacy

/-! # Actual matrix representatives for the two symplectic lift types -/
noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

private def signValue (S : Finset (Fin n)) (i : Fin n) : F := if i ∈ S then -1 else 1

private theorem signValue_square (S : Finset (Fin n)) (i : Fin n) :
    signValue (F := F) S i * signValue S i = 1 := by
  simp only [signValue]; split <;> simp

private def signLinear (S : Finset (Fin n)) : Vector n F ≃ₗ[F] Vector n F where
  toFun x i := signValue S (Sum.elim id id i) * x i
  invFun x i := signValue S (Sum.elim id id i) * x i
  left_inv x := by funext i; simp only [←mul_assoc,signValue_square,one_mul]
  right_inv x := by funext i; simp only [←mul_assoc,signValue_square,one_mul]
  map_add' x y := by funext i; exact mul_add _ _ _
  map_smul' c x := by funext i; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

private theorem signLinear_preserves (S : Finset (Fin n)) (x y : Vector n F) :
    form (signLinear S x) (signLinear S y) = form x y := by
  simp only [form_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (signValue S i * x (.inl i)) * (signValue S i * y (.inr i)) -
    (signValue S i * x (.inr i)) * (signValue S i * y (.inl i)) = _
  calc
    _ = (signValue S i * signValue S i) *
      (x (.inl i)*y (.inr i)-x (.inr i)*y (.inl i)) := by ring
    _ = _ := by rw [signValue_square,one_mul]

def signRepresentative (S : Finset (Fin n)) : Sp n F := ofLinear (signLinear S) (signLinear_preserves S)

@[simp] theorem signRepresentative_apply (S : Finset (Fin n)) (x : Vector n F) (i : Index n) :
    ((signRepresentative S : Sp n F) • x) i =
      (if Sum.elim id id i ∈ S then -1 else 1) * x i := by
  rw [signRepresentative,ofLinear_apply]; rfl

theorem signRepresentative_square (S : Finset (Fin n)) :
    (signRepresentative S : Sp n F)^2=1 := by
  apply ext_action
  intro x
  funext i
  simp only [pow_two,mul_smul,signRepresentative_apply,one_smul]
  split <;> simp

private def complexLinear : Vector n F ≃ₗ[F] Vector n F where
  toFun x := Sum.elim (fun i => -x (.inr i)) (fun i => x (.inl i))
  invFun x := Sum.elim (fun i => x (.inr i)) (fun i => -x (.inl i))
  left_inv x := by funext i; cases i <;> simp
  right_inv x := by funext i; cases i <;> simp
  map_add' x y := by funext i; cases i <;> simp [add_comm]
  map_smul' c x := by funext i; cases i <;> simp

private theorem complexLinear_preserves (x y : Vector n F) :
    form (complexLinear x) (complexLinear y) = form x y := by
  simp only [form_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (-x (.inr i))*y (.inl i)-x (.inl i)*(-y (.inr i)) = _
  ring

def complexRepresentative : Sp n F := ofLinear complexLinear complexLinear_preserves

@[simp] theorem complexRepresentative_apply_left (x : Vector n F) (i : Fin n) :
    ((complexRepresentative : Sp n F) • x) (.inl i) = -x (.inr i) := by
  rw [complexRepresentative,ofLinear_apply]; rfl

@[simp] theorem complexRepresentative_apply_right (x : Vector n F) (i : Fin n) :
    ((complexRepresentative : Sp n F) • x) (.inr i) = x (.inl i) := by
  rw [complexRepresentative,ofLinear_apply]; rfl

theorem complexRepresentative_square : (complexRepresentative : Sp n F)^2 = negativeIdentity := by
  apply ext_action
  intro x
  funext i
  cases i <;> simp [pow_two,mul_smul]

theorem complexRepresentative_not_central (hn : 0<n) :
    (complexRepresentative : Sp n F) ∉ Subgroup.center (Sp n F) := by
  intro hc
  rcases (center_iff_eq_one_or_negativeIdentity hn _).mp hc with he|he
  all_goals
    have hh := congrArg (fun g : Sp n F => (g • e (F := F) ⟨0,hn⟩) (.inr ⟨0,hn⟩)) he
    simpa [e] using hh

end Atlas.Symplectic

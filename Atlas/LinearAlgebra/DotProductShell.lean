import Atlas.LinearAlgebra.DotProductFiber

/-! Counting nonzero levels of a split quadratic form by linear fibres. -/
noncomputable section
namespace Atlas.DotProduct
variable {n : ℕ} {F : Type*} [Field F]

def shellFiberEquiv (a : F) :
    {p : (Fin n → F) × (Fin n → F) // functional p.1 p.2 = a} ≃
      Σ x : Fin n → F, {y : Fin n → F // functional x y = a} where
  toFun p := ⟨p.val.1, p.val.2, p.prop⟩
  invFun p := ⟨(p.1,p.2.val),p.2.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_nonzero_shell [Finite F] (a : F) (ha : a ≠ 0) :
    Nat.card {p : (Fin n → F) × (Fin n → F) // functional p.1 p.2 = a} =
      (Nat.card F ^ n - 1) * Nat.card F ^ (n-1) := by
  classical
  letI := Fintype.ofFinite F
  rw [Nat.card_congr (shellFiberEquiv a),Nat.card_sigma]
  have hc (x : Fin n → F) : Nat.card {y // functional x y=a} =
      if x=0 then 0 else Nat.card F ^ (n-1) := by
    split_ifs with hx
    · subst x
      haveI : IsEmpty {y : Fin n → F // functional (0 : Fin n → F) y=a} :=
        ⟨fun y => ha (by simpa using y.prop.symm)⟩
      exact Nat.card_of_isEmpty
    · exact card_fiber x hx a
  simp_rw [hc]
  rw [Finset.sum_ite]
  simp [Finset.filter_ne',Nat.card_eq_fintype_card]

end Atlas.DotProduct

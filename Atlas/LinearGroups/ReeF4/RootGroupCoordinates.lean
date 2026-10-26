import Atlas.LinearGroups.ReeF4.ShortRootCoordinates

/-! Draft direct polynomial coordinates for the Suzuki-type short-root group.
No group membership is asserted here until the torus-conjugation identities
and zero-parameter cases are proved. -/
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def shortRootParameterFormula (τ : F →+* F) (a : F) (w : Carrier F) : Carrier F :=
  (![w.1 0, w.1 1 + a*w.2 0 4 + a*τ a*w.2 0 5,
      w.1 2 + a*w.2 0 4 + a*τ a*w.2 0 5],
   ![![w.2 0 0, w.2 0 1,
        w.2 0 2 + τ a*w.2 0 3 + a^2*τ a*w.2 0 4 + a^2*(τ a)^2*w.2 0 5,
        w.2 0 3 + a*(w.1 1+w.1 2) + a^2*w.2 0 4,
        w.2 0 4 + τ a*w.2 0 5, w.2 0 5, w.2 0 6, w.2 0 7],
     ![w.2 1 0 + τ a*w.2 1 1, w.2 1 1 + a*w.2 2 1,
        w.2 1 2 + a^2*τ a*w.2 1 3 + a*w.2 2 2 + a*τ a*w.2 2 4,
        w.2 1 3,
        w.2 1 4 + a^2*τ a*w.2 1 5 + a*w.2 2 3 + a*τ a*w.2 2 5,
        w.2 1 5, w.2 1 6 + τ a*w.2 1 7, w.2 1 7 + a*w.2 2 7],
     ![w.2 2 0 + a*w.2 1 0 + a*τ a*w.2 1 1 + a^2*τ a*w.2 2 1,
        w.2 2 1, w.2 2 2 + τ a*w.2 2 4, w.2 2 3 + τ a*w.2 2 5,
        w.2 2 4 + a*w.2 1 3, w.2 2 5 + a*w.2 1 5,
        w.2 2 6 + a*w.2 1 6 + a*τ a*w.2 1 7 + a^2*τ a*w.2 2 7,
        w.2 2 7]])

def shortRootCenterFormula (τ : F →+* F) (b : F) (w : Carrier F) : Carrier F :=
  (![w.1 0, w.1 1 + b*w.2 0 5, w.1 2 + b*w.2 0 5],
   ![![w.2 0 0, w.2 0 1,
        w.2 0 2 + b*(w.1 1+w.1 2) + τ b*w.2 0 4 + b^2*w.2 0 5,
        w.2 0 3 + τ b*w.2 0 5, w.2 0 4, w.2 0 5, w.2 0 6, w.2 0 7],
     ![w.2 1 0 + b*w.2 2 1, w.2 1 1,
        w.2 1 2 + τ b*w.2 1 3 + b*w.2 2 4, w.2 1 3,
        w.2 1 4 + τ b*w.2 1 5 + b*w.2 2 5, w.2 1 5,
        w.2 1 6 + b*w.2 2 7, w.2 1 7],
     ![w.2 2 0 + b*w.2 1 1 + τ b*w.2 2 1, w.2 2 1,
        w.2 2 2 + b*w.2 1 3, w.2 2 3 + b*w.2 1 5,
        w.2 2 4, w.2 2 5,
        w.2 2 6 + b*w.2 1 7 + τ b*w.2 2 7, w.2 2 7]])



theorem shortRootParameterFormula_trace (τ : F →+* F) (a : F) (w : Carrier F) :
    trace (shortRootParameterFormula τ a w) = trace w := by
  simp [shortRootParameterFormula, trace]
  linear_combination (a*w.2 0 4 + a*τ a*w.2 0 5) * (CharTwo.two_eq_zero (R := F))

def shortRootParameterLinear (τ : F →+* F) (a : F) : TraceZero F →ₗ[F] TraceZero F where
  toFun w := ⟨shortRootParameterFormula τ a w.val, by
    change trace (shortRootParameterFormula τ a w.val) = 0
    rw [shortRootParameterFormula_trace]
    exact w.property⟩
  map_add' u v := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [shortRootParameterFormula] <;> ring
    · funext i j
      fin_cases i <;> fin_cases j <;> simp [shortRootParameterFormula] <;> ring
  map_smul' c u := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [shortRootParameterFormula, smul_eq_mul] <;> ring
    · funext i j
      fin_cases i <;> fin_cases j <;> simp [shortRootParameterFormula, smul_eq_mul] <;> ring

@[simp] theorem shortRootParameterLinear_val (τ : F →+* F) (a : F) (w : TraceZero F) :
    (shortRootParameterLinear τ a w).val = shortRootParameterFormula τ a w.val := rfl

@[simp] theorem shortRootParameterFormula_zero (τ : F →+* F) (w : Carrier F) :
    shortRootParameterFormula τ 0 w = w := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [shortRootParameterFormula]
  · funext i j
    fin_cases i <;> fin_cases j <;> simp [shortRootParameterFormula]

theorem shortRootCenterFormula_trace (τ : F →+* F) (b : F) (w : Carrier F) :
    trace (shortRootCenterFormula τ b w) = trace w := by
  simp [shortRootCenterFormula, trace]
  linear_combination (b*w.2 0 5) * (CharTwo.two_eq_zero (R := F))

def shortRootCenterLinear (τ : F →+* F) (b : F) : TraceZero F →ₗ[F] TraceZero F where
  toFun w := ⟨shortRootCenterFormula τ b w.val, by
    change trace (shortRootCenterFormula τ b w.val) = 0
    rw [shortRootCenterFormula_trace]
    exact w.property⟩
  map_add' u v := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [shortRootCenterFormula] <;> ring
    · funext i j
      fin_cases i <;> fin_cases j <;> simp [shortRootCenterFormula] <;> ring
  map_smul' c u := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [shortRootCenterFormula, smul_eq_mul] <;> ring
    · funext i j
      fin_cases i <;> fin_cases j <;> simp [shortRootCenterFormula, smul_eq_mul] <;> ring

@[simp] theorem shortRootCenterLinear_val (τ : F →+* F) (b : F) (w : TraceZero F) :
    (shortRootCenterLinear τ b w).val = shortRootCenterFormula τ b w.val := rfl

@[simp] theorem shortRootCenterFormula_zero (τ : F →+* F) (w : Carrier F) :
    shortRootCenterFormula τ 0 w = w := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [shortRootCenterFormula]
  · funext i j
    fin_cases i <;> fin_cases j <;> simp [shortRootCenterFormula]

theorem shortRootParameterFormula_one (τ : F →+* F) (w : Carrier F) :
    shortRootParameterFormula τ 1 w = shortRootFormula w := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [shortRootParameterFormula, shortRootFormula] <;> ring
  · funext i j
    fin_cases i <;> fin_cases j <;> simp [shortRootParameterFormula, shortRootFormula] <;> ring

end Atlas.ReeF4

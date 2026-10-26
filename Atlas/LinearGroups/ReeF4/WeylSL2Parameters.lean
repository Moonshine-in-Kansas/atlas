import Atlas.LinearGroups.ReeF4.LongRootCoordinateComparison
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.SetTheory.Cardinal.NatCard

/-! The two additive parameters in the concrete long-root SL₂ representation.
The second parameter will be specialized to the Tits image of the first.
No membership in the full Ree stabilizer is asserted in this algebraic file. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def longSL2Formula (u z : F) (w : Carrier F) : Carrier F :=
  (![w.1 0 + u*w.2 1 4, w.1 1, w.1 2 + u*w.2 1 4],
   ![![w.2 0 0 + u*w.2 2 0, w.2 0 1 + z*w.2 0 2, w.2 0 2, w.2 0 3,
        w.2 0 4 + u*w.2 2 3,
        w.2 0 5 + z*w.2 0 6 + u*w.2 2 5 + u*z*w.2 2 6,
        w.2 0 6 + u*w.2 2 6, w.2 0 7],
     ![w.2 1 0, w.2 1 1 + z*w.2 1 2, w.2 1 2,
        w.2 1 3 + u*(w.1 0+w.1 2) + u^2*w.2 1 4,
        w.2 1 4, w.2 1 5 + z*w.2 1 6, w.2 1 6, w.2 1 7],
     ![w.2 2 0,
        w.2 2 1 + u*w.2 0 1 + u*z*w.2 0 2 + z*w.2 2 2,
        w.2 2 2 + u*w.2 0 2, w.2 2 3,
        w.2 2 4 + u*w.2 0 3, w.2 2 5 + z*w.2 2 6, w.2 2 6,
        w.2 2 7 + u*w.2 0 7]])

theorem longSL2Formula_trace (u z : F) (w : Carrier F) :
    trace (longSL2Formula u z w) = trace w := by
  simp [longSL2Formula, trace]
  linear_combination u * w.2 1 4 * (CharTwo.two_eq_zero (R := F))

def longSL2Linear (u z : F) : TraceZero F →ₗ[F] TraceZero F where
  toFun w := ⟨longSL2Formula u z w.val, by
    change trace (longSL2Formula u z w.val) = 0
    rw [longSL2Formula_trace]
    exact w.property⟩
  map_add' w v := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [longSL2Formula] <;> ring
    · funext i j
      fin_cases i <;> fin_cases j <;> simp [longSL2Formula] <;> ring
  map_smul' a w := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [longSL2Formula, smul_eq_mul] <;> ring
    · funext i j
      fin_cases i <;> fin_cases j <;> simp [longSL2Formula, smul_eq_mul] <;> ring

theorem longSL2Formula_zero (w : Carrier F) : longSL2Formula 0 0 w = w := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [longSL2Formula]
  · funext i j
    fin_cases i <;> fin_cases j <;> simp [longSL2Formula]

set_option maxHeartbeats 800000 in
theorem longSL2Formula_comp (u z v t : F) (w : Carrier F) :
    longSL2Formula u z (longSL2Formula v t w) =
      longSL2Formula (u+v) (z+t) w := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [longSL2Formula] <;> ring
  · funext i j
    fin_cases i <;> fin_cases j <;> simp [longSL2Formula] <;>
      ring_nf <;> simp [CharTwo.two_eq_zero]

theorem longSL2Linear_involutive (u z : F) :
    Function.Involutive (longSL2Linear u z) := by
  intro w
  apply Subtype.ext
  change longSL2Formula u z (longSL2Formula u z w.val) = w.val
  rw [longSL2Formula_comp, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
    longSL2Formula_zero]

def longSL2Equiv (u z : F) : TraceZero F ≃ₗ[F] TraceZero F :=
  LinearEquiv.ofInvolutive (longSL2Linear u z) (longSL2Linear_involutive u z)

theorem longSL2Equiv_mul (u z v t : F) :
    longSL2Equiv u z * longSL2Equiv v t = longSL2Equiv (u+v) (z+t) := by
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  exact longSL2Formula_comp u z v t w.val

@[simp] theorem longSL2Equiv_zero : longSL2Equiv (0 : F) 0 = 1 := by
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  exact longSL2Formula_zero w.val

theorem longSL2Formula_one (w : Carrier F) :
    longSL2Formula 1 1 w = longRootFormula w := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [longSL2Formula, longRootFormula]
  · funext i j
    fin_cases i <;> fin_cases j <;> simp [longSL2Formula, longRootFormula] <;> ring

theorem longSL2Equiv_one : longSL2Equiv (1 : F) 1 = longRootEquiv := by
  apply LinearEquiv.ext
  intro w
  change longSL2Linear 1 1 w = longRootLinear w
  rw [← longRootCoordinateLinear_eq]
  apply Subtype.ext
  exact longSL2Formula_one w.val

/-- Every additive field twist gives an actual additive family of long-root operators. -/
def longSL2ParameterHom (σ : F →+* F) : Multiplicative F →*
    (TraceZero F ≃ₗ[F] TraceZero F) where
  toFun u := longSL2Equiv u.toAdd (σ u.toAdd)
  map_one' := by simp
  map_mul' u v := by
    change longSL2Equiv (u.toAdd+v.toAdd) (σ (u.toAdd+v.toAdd)) = _
    rw [_root_.map_add, longSL2Equiv_mul]

theorem longSL2ParameterHom_injective (σ : F →+* F) :
    Function.Injective (longSL2ParameterHom σ) := by
  intro u v h
  have h0 := congrArg
    (fun e : TraceZero F ≃ₗ[F] TraceZero F => (e (rootVector (2,0))).val.2 0 0) h
  simpa [longSL2ParameterHom, longSL2Equiv, longSL2Linear, longSL2Formula,
    rootVector, Pi.single_apply] using h0

theorem longSL2ParameterHom_at_one (σ : F →+* F) :
    longSL2ParameterHom σ (Multiplicative.ofAdd (1 : F)) = longRootEquiv := by
  change longSL2Equiv 1 (σ 1) = longRootEquiv
  rw [map_one, longSL2Equiv_one]

/-- The concrete additive root subgroup, without an ambient Ree membership claim. -/
def longSL2RootSubgroup (σ : F →+* F) :
    Subgroup (TraceZero F ≃ₗ[F] TraceZero F) := (longSL2ParameterHom σ).range

def longSL2RootEquiv (σ : F →+* F) :
    Multiplicative F ≃* longSL2RootSubgroup σ :=
  MonoidHom.ofInjective (longSL2ParameterHom_injective σ)

theorem card_longSL2RootSubgroup (σ : F →+* F) :
    Nat.card (longSL2RootSubgroup σ) = Nat.card F := by
  rw [← Nat.card_congr (longSL2RootEquiv σ).toEquiv]
  rfl

end Atlas.ReeF4

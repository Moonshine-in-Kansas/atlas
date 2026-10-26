import Atlas.LinearGroups.F4.Weights
import Atlas.Algebra.Albert.ScalarMap

noncomputable section
namespace Atlas.F4
variable {F : Type*} [CommRing F]

abbrev TorusParameters (F : Type*) [CommRing F] := Fin 4 → Fˣ

def weightCharacter (v : RootData.Vector) : TorusParameters F →* Fˣ where
  toFun t := ∏ i : Fin 4, t i ^ v i
  map_one' := by simp
  map_mul' s t := by simp [mul_zpow, Finset.prod_mul_distrib]

def torusScale (t : TorusParameters F) (i : Fin 3) (j : Fin 8) : Fˣ :=
  weightCharacter (RootData.simpleCoefficients (Weights.slotRoot (i,j))) t

def torusApply (t : TorusParameters F) (x : Atlas.Albert.Carrier F) : Atlas.Albert.Carrier F :=
  (x.1, fun i j => (torusScale t i j : F) * x.2 i j)

def torusEquiv (t : TorusParameters F) :
    Atlas.Albert.Carrier F ≃ₗ[F] Atlas.Albert.Carrier F where
  toFun := torusApply t
  invFun x := (x.1, fun i j => (((torusScale t i j)⁻¹ : Fˣ) : F) * x.2 i j)
  left_inv x := by
    apply Prod.ext
    · rfl
    · funext i j; simp [torusApply, ← mul_assoc]
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext i j; simp [torusApply, ← mul_assoc]
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext i j; simp [torusApply, mul_add]
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · funext i j; simp [torusApply]; ring

theorem torusEquiv_apply (t : TorusParameters F) (x : Atlas.Albert.Carrier F) :
    torusEquiv t x = torusApply t x := rfl

theorem torusEquiv_unit (t : TorusParameters F) :
    torusEquiv t Atlas.Albert.unit = Atlas.Albert.unit := by
  apply Prod.ext
  · rfl
  · funext i j; simp [torusEquiv, torusApply, Atlas.Albert.unit]

theorem torusEquiv_one : torusEquiv (1 : TorusParameters F) = 1 := by
  apply LinearEquiv.ext
  intro x
  apply Prod.ext
  · rfl
  · funext i j; simp [torusEquiv, torusApply, torusScale]

theorem torusEquiv_mul (s t : TorusParameters F) :
    torusEquiv (s * t) = torusEquiv s * torusEquiv t := by
  apply LinearEquiv.ext
  intro x
  apply Prod.ext
  · rfl
  · funext i j; simp [torusEquiv, torusApply, torusScale, mul_assoc]

def diagonalTorusLinear : TorusParameters F →*
    (Atlas.Albert.Carrier F ≃ₗ[F] Atlas.Albert.Carrier F) where
  toFun := torusEquiv
  map_one' := torusEquiv_one
  map_mul' := torusEquiv_mul

theorem torusScale_C3 (t : TorusParameters F) : torusScale t 2 3 = t 2 := by
  simp [torusScale, weightCharacter, RootData.simpleCoefficients, RootData.coordinates,
    Weights.slotRoot, Fin.prod_univ_succ]

theorem torusScale_A3 (t : TorusParameters F) : torusScale t 0 3 = t 3 := by
  simp [torusScale, weightCharacter, RootData.simpleCoefficients, RootData.coordinates,
    Weights.slotRoot, Fin.prod_univ_succ]

theorem torusScale_C2 (t : TorusParameters F) : torusScale t 2 2 = t 1 * t 2 := by
  simp [torusScale, weightCharacter, RootData.simpleCoefficients, RootData.coordinates,
    Weights.slotRoot, Fin.prod_univ_succ]

theorem torusScale_C1 (t : TorusParameters F) : torusScale t 2 1 = t 0 * t 1 * t 2 := by
  simp [torusScale, weightCharacter, RootData.simpleCoefficients, RootData.coordinates,
    Weights.slotRoot, Fin.prod_univ_succ, mul_assoc]

theorem diagonalTorusLinear_injective : Function.Injective (diagonalTorusLinear (F := F)) := by
  intro s t h
  have hs : ∀ i : Fin 3, ∀ j : Fin 8, torusScale s i j = torusScale t i j := by
    intro i j
    apply Units.ext
    have hh := congrArg (fun g : Atlas.Albert.Carrier F ≃ₗ[F] Atlas.Albert.Carrier F =>
      (g (0, fun _ _ => 1)).2 i j) h
    simpa [diagonalTorusLinear, torusEquiv, torusApply] using hh
  have h2 : s 2 = t 2 := by simpa only [torusScale_C3] using hs 2 3
  have h3 : s 3 = t 3 := by simpa only [torusScale_A3] using hs 0 3
  have h1 : s 1 = t 1 := by
    have hh := hs 2 2
    rw [torusScale_C2, torusScale_C2, h2] at hh
    exact mul_right_cancel hh
  have h0 : s 0 = t 0 := by
    have hh := hs 2 1
    rw [torusScale_C1, torusScale_C1, h1, h2] at hh
    exact mul_right_cancel (mul_right_cancel hh)
  funext i
  fin_cases i <;> assumption

end Atlas.F4

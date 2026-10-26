import Atlas.LinearGroups.SuzukiFamily.Unipotent
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! The actual projective Suzuki ovoid, independently of its group stabilizer. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
abbrev Vector (F : Type*) := Fin 4 → F
abbrev Projective (F : Type*) [Field F] := Projectivization F (Vector F)

def affineVector (m : ℕ) (a b : F) : Vector F :=
  ![1,a,a*theta F m a+b,norm m a b]
def infinityVector : Vector F := ![0,0,0,1]

theorem affineVector_ne_zero (m : ℕ) (a b : F) : affineVector m a b ≠ 0 := by
  intro he
  have := congrFun he 0
  simpa [affineVector] using this

theorem infinityVector_ne_zero : (infinityVector : Vector F) ≠ 0 := by
  intro he
  have := congrFun he 3
  simpa [infinityVector] using this

def affinePoint (m : ℕ) (a b : F) : Projective F :=
  Projectivization.mk F (affineVector m a b) (affineVector_ne_zero m a b)
def infinityPoint : Projective F :=
  Projectivization.mk F infinityVector infinityVector_ne_zero

theorem affinePoint_injective (m : ℕ) :
    Function.Injective (fun p : F × F => affinePoint m p.1 p.2) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ he
  obtain ⟨t,ht⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp he
  have ht1 : (t:F)=1 := by
    simpa [affineVector,Pi.smul_apply,Units.smul_def] using congrFun ht 0
  have hv : affineVector m c d=affineVector m a b := by simpa [Units.smul_def,ht1] using ht
  have hc : c=a := congrFun hv 1
  subst c
  have hd : d=b := by simpa [affineVector] using congrFun hv 2
  subst d
  rfl

theorem infinity_ne_affine (m : ℕ) (a b : F) : infinityPoint ≠ affinePoint m a b := by
  intro he
  obtain ⟨t,ht⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp he
  have ht0 : (t:F)=0 := by simpa [affineVector,infinityVector,Pi.smul_apply,Units.smul_def] using congrFun ht 0
  exact Units.ne_zero t ht0

def pointParam (m : ℕ) : Option (F × F) → Projective F
  | none => infinityPoint
  | some (a,b) => affinePoint m a b

theorem pointParam_injective (m : ℕ) : Function.Injective (pointParam (F := F) m) := by
  intro p q he
  cases p with
  | none =>
    cases q with
    | none => rfl
    | some q => exact False.elim (infinity_ne_affine m q.1 q.2 he)
  | some p =>
    cases q with
    | none => exact False.elim (infinity_ne_affine m p.1 p.2 he.symm)
    | some q => exact congrArg some (affinePoint_injective m he)

def pointSet (m : ℕ) : Set (Projective F) := Set.range (pointParam m)
def pointEquiv (m : ℕ) : Option (F × F) ≃ pointSet (F := F) m :=
  Equiv.ofInjective (pointParam m) (pointParam_injective m)

theorem card_pointSet (m : ℕ) : Nat.card (pointSet (F := F) m) = (Nat.card F)^2+1 := by
  rw [← Nat.card_congr (pointEquiv (F := F) m),Finite.card_option,Nat.card_prod,pow_two]
end Atlas.SuzukiFamily

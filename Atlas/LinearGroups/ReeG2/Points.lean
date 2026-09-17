import Atlas.LinearGroups.ReeG2.RootMatrices
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.SetTheory.Cardinal.NatCard

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

abbrev Vector (F : Type*) := Fin 7 → F
abbrev Projective (F : Type*) [Field F] := Projectivization F (Vector F)

def affineVector (m : ℕ) (a b c : F) : Vector F := rootMatrix m a b c 0

theorem affineVector_zero (m : ℕ) (a b c : F) : affineVector m a b c 0 = 1 := by
  simp [affineVector, rootMatrix_expanded, rootExpanded]

theorem affineVector_ne_zero (m : ℕ) (a b c : F) : affineVector m a b c ≠ 0 := by
  intro h
  have := congrFun h 0
  simpa [affineVector_zero] using this

def affinePoint (m : ℕ) (a b c : F) : Projective F :=
  Projectivization.mk F (affineVector m a b c) (affineVector_ne_zero m a b c)

def infinityVector : Vector F := ![0,0,0,0,0,0,1]

theorem infinityVector_ne_zero : (infinityVector : Vector F) ≠ 0 := by
  intro h
  have := congrFun h 6
  simpa [infinityVector] using this

def infinityPoint : Projective F :=
  Projectivization.mk F infinityVector infinityVector_ne_zero

theorem affinePoint_injective (m : ℕ) : Function.Injective
    (fun p : F × F × F => affinePoint m p.1 p.2.1 p.2.2) := by
  rintro ⟨a,b,c⟩ ⟨d,e,f⟩ h
  obtain ⟨l,hl⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp h
  have hzero := congrFun hl 0
  have hlone : (l : F) = 1 := by simpa [Pi.smul_apply, Units.smul_def, affineVector_zero] using hzero
  have hv : affineVector m d e f = affineVector m a b c := by
    simpa [Units.smul_def, hlone] using hl
  have ha := congrFun hv 1
  have hb := congrFun hv 2
  have hc := congrFun hv 3
  simp only [affineVector, rootMatrix_01] at ha
  simp only [affineVector, rootMatrix_02, neg_inj] at hb
  have hda := (theta F m).injective ha
  have heb := (theta F m).injective hb
  subst d; subst e
  simp only [affineVector, rootMatrix_03, sub_right_inj] at hc
  have hfc := (theta F m).injective hc
  subst f
  rfl

theorem infinity_ne_affine (m : ℕ) (a b c : F) : infinityPoint ≠ affinePoint m a b c := by
  intro h
  obtain ⟨l,hl⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp h
  have hz := congrFun hl 0
  have : (l : F) = 0 := by
    simpa [Pi.smul_apply, Units.smul_def, affineVector_zero, infinityVector] using hz
  exact Units.ne_zero l this

def pointParam (m : ℕ) : Option (F × F × F) → Projective F
  | none => infinityPoint
  | some (a,b,c) => affinePoint m a b c

theorem pointParam_injective (m : ℕ) : Function.Injective (pointParam (F := F) m) := by
  intro p q h
  cases p with
  | none =>
    cases q with
    | none => rfl
    | some q => exact False.elim (infinity_ne_affine m q.1 q.2.1 q.2.2 h)
  | some p =>
    cases q with
    | none => exact False.elim (infinity_ne_affine m p.1 p.2.1 p.2.2 h.symm)
    | some q => exact congrArg some (affinePoint_injective m h)

/-- The actual projective point set; invariance under the generators is a separate obligation. -/
def pointSet (m : ℕ) : Set (Projective F) := Set.range (pointParam m)

def pointEquiv (m : ℕ) : Option (F × F × F) ≃ pointSet (F := F) m :=
  Equiv.ofInjective (pointParam m) (pointParam_injective m)

theorem card_pointSet (m : ℕ) : Nat.card (pointSet (F := F) m) = Nat.card F ^ 3 + 1 := by
  rw [← Nat.card_congr (pointEquiv (F := F) m), Finite.card_option,
    Nat.card_prod, Nat.card_prod]
  ring
end Atlas.ReeG2

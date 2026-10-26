import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Module

/-! Finite minuscule strings and their integral operators.
No concrete selected orbit, lattice-span assertion, group order or simplicity
is assumed to exist. Those remain separate providers. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule

/-- The exact local data extracted from a minuscule Weyl orbit. Pairing values
are integer grades before any change of coefficient ring. -/
structure Strings (I Ω : Type*) where
  pairing : I → Ω → ℤ
  reflection : I → Equiv.Perm Ω
  involutive : ∀ i, Function.Involutive (reflection i)
  pairing_reflection : ∀ i μ, pairing i (reflection i μ) = -pairing i μ
  minuscule : ∀ i μ, pairing i μ = -1 ∨ pairing i μ = 0 ∨ pairing i μ = 1

namespace Strings
variable {I Ω : Type*} (S : Strings I Ω)
variable (R : Type*) [CommRing R]

/-- Finite-support orbit module, with its literal singleton weight basis. -/
abbrev OrbitModule := Ω →₀ R

/-- Raising for sign -1 and lowering for sign +1. All matrix coefficients are 0 or 1. -/
def step (i : I) (ε : ℤ) : Module.End R (OrbitModule (Ω := Ω) R) :=
  Finsupp.linearCombination R fun μ =>
    if S.pairing i μ = ε then Finsupp.single (S.reflection i μ) 1 else 0

@[simp] theorem step_single (i : I) (ε : ℤ) (μ : Ω) (r : R) :
    S.step R i ε (Finsupp.single μ r) =
      if S.pairing i μ = ε then Finsupp.single (S.reflection i μ) r else 0 := by
  classical
  simp [step]

/-- The second step vanishes because the paired weight has the opposite sign. -/
theorem step_square (i : I) (ε : ℤ) (hε : ε ≠ 0) :
    S.step R i ε * S.step R i ε = 0 := by
  apply Finsupp.lhom_ext
  intro μ r
  change S.step R i ε (S.step R i ε (Finsupp.single μ r)) = 0
  by_cases h : S.pairing i μ = ε
  · have hn : S.pairing i (S.reflection i μ) ≠ ε := by
      rw [S.pairing_reflection, h]
      omega
    simp [h, hn]
  · simp [h]

abbrev raising (i : I) := S.step R i (-1)
abbrev lowering (i : I) := S.step R i 1

@[simp] theorem raising_square (i : I) : S.raising R i * S.raising R i = 0 :=
  S.step_square R i (-1) (by decide)

@[simp] theorem lowering_square (i : I) : S.lowering R i * S.lowering R i = 0 :=
  S.step_square R i 1 (by decide)

/-- An actual additive one-parameter map over every commutative ring,
including characteristics two and three. -/
def transvection (i : I) (ε : ℤ) (t : R) : Module.End R (OrbitModule (Ω := Ω) R) :=
  1 + t • S.step R i ε

@[simp] theorem transvection_apply (i : I) (ε : ℤ) (t : R)
    (v : OrbitModule (Ω := Ω) R) :
    S.transvection R i ε t v = v + t • S.step R i ε v := rfl

theorem transvection_add (i : I) (ε : ℤ) (hε : ε ≠ 0) (s t : R) :
    S.transvection R i ε (s + t) =
      S.transvection R i ε s * S.transvection R i ε t := by
  apply LinearMap.ext
  intro v
  have hz : S.step R i ε (S.step R i ε v) = 0 :=
    congrArg (fun f : Module.End R (OrbitModule (Ω := Ω) R) => f v)
      (S.step_square R i ε hε)
  simp [Module.End.mul_apply, transvection_apply, map_add, map_smul, hz, add_smul]
  module

@[simp] theorem transvection_zero (i : I) (ε : ℤ) : S.transvection R i ε 0 = 1 := by
  simp [transvection]

theorem transvection_inverse (i : I) (ε : ℤ) (hε : ε ≠ 0) (t : R) :
    S.transvection R i ε t * S.transvection R i ε (-t) = 1 := by
  rw [← S.transvection_add R i ε hε, add_neg_cancel, transvection_zero]

/-- Invertible root operator, with the inverse parameter -t proved explicitly. -/
def rootEquiv (i : I) (ε : ℤ) (hε : ε ≠ 0) (t : R) :
    OrbitModule (Ω := Ω) R ≃ₗ[R] OrbitModule (Ω := Ω) R :=
  LinearEquiv.ofLinearMap (S.transvection R i ε t) (S.transvection R i ε (-t))
    (by simpa only [Module.End.mul_eq_comp, Module.End.one_eq_id, neg_neg] using S.transvection_inverse R i ε hε t)
    (by simpa only [Module.End.mul_eq_comp, Module.End.one_eq_id, neg_neg] using S.transvection_inverse R i ε hε (-t))

end Strings
end Atlas.Chevalley.Integral.Minuscule

namespace Atlas.Chevalley.Integral.Minuscule.Strings
variable {I Ω : Type*} [Fintype Ω] [DecidableEq Ω] (S : Strings I Ω)
  (R : Type*) [CommRing R]

def stepMatrix (i : I) (ε : ℤ) : Matrix Ω Ω R :=
  LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne (S.step R i ε)

theorem stepMatrix_entry (i : I) (ε : ℤ) (μ ν : Ω) :
    S.stepMatrix R i ε μ ν =
      if S.pairing i ν = ε ∧ S.reflection i ν = μ then 1 else 0 := by
  rw [stepMatrix, LinearMap.toMatrix_apply]
  change S.step R i ε (Finsupp.single ν 1) μ = _
  rw [step_single]
  by_cases h : S.pairing i ν = ε <;> simp [h, Finsupp.single_apply]

theorem stepMatrix_square (i : I) (ε : ℤ) (hε : ε ≠ 0) :
    S.stepMatrix R i ε * S.stepMatrix R i ε = 0 := by
  have hm := congrArg (LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne)
    (S.step_square R i ε hε)
  simpa only [LinearMap.toMatrix_mul, map_zero, stepMatrix] using hm

def rootMatrix (i : I) (ε : ℤ) (t : R) : Matrix Ω Ω R := 1+t • S.stepMatrix R i ε

theorem rootMatrix_eq_toMatrix (i : I) (ε : ℤ) (t : R) :
    S.rootMatrix R i ε t = LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
      (S.transvection R i ε t) := by
  simp only [rootMatrix, transvection, map_add, map_smul, LinearMap.toMatrix_one, stepMatrix]

theorem rootMatrix_add (i : I) (ε : ℤ) (hε : ε ≠ 0) (s t : R) :
    S.rootMatrix R i ε (s+t) = S.rootMatrix R i ε s * S.rootMatrix R i ε t := by
  simp only [rootMatrix_eq_toMatrix, transvection_add S R i ε hε, LinearMap.toMatrix_mul]

@[simp] theorem rootMatrix_zero (i : I) (ε : ℤ) : S.rootMatrix R i ε 0 = 1 := by
  simp [rootMatrix]

def rootMatrixUnit (i : I) (ε : ℤ) (hε : ε ≠ 0) (t : R) : (Matrix Ω Ω R)ˣ where
  val := S.rootMatrix R i ε t
  inv := S.rootMatrix R i ε (-t)
  val_inv := by rw [← rootMatrix_add S R i ε hε, add_neg_cancel, rootMatrix_zero]
  inv_val := by rw [← rootMatrix_add S R i ε hε, neg_add_cancel, rootMatrix_zero]

def rootMatrixHom (i : I) (ε : ℤ) (hε : ε ≠ 0) :
    Multiplicative R →* (Matrix Ω Ω R)ˣ where
  toFun t := S.rootMatrixUnit R i ε hε t.toAdd
  map_one' := Units.ext (rootMatrix_zero S R i ε)
  map_mul' s t := Units.ext (rootMatrix_add S R i ε hε s.toAdd t.toAdd)

end Atlas.Chevalley.Integral.Minuscule.Strings

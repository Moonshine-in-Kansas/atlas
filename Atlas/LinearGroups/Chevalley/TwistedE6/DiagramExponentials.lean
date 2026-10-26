import Atlas.LinearGroups.Chevalley.TwistedE6.DiagramOperators
import Atlas.LinearGroups.Chevalley.Integral.GeckExponential
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Integral diagram covariance extends to divided powers before reduction
to a coefficient ring. In particular no division by 2 or 3 is made in the
target field. -/
noncomputable section
open scoped Matrix
namespace Atlas.Chevalley.TwistedE6
open E6Data Integral
local instance : Fintype Root := Fintype.ofFinite Root
local instance : InvolutiveNeg Root := pairing.indexNeg

variable (R : Type*) [CommRing R]

def matrixDiagram :
    Matrix (base.support ⊕ Root) (base.support ⊕ Root) R ≃+*
      Matrix (base.support ⊕ Root) (base.support ⊕ Root) R :=
  Matrix.reindexRingEquiv R adjointIndexDiagram.symm

@[simp] theorem matrixDiagram_apply (A : Matrix (base.support ⊕ Root) (base.support ⊕ Root) R)
    (a c : base.support ⊕ Root) :
    matrixDiagram R A a c = A (adjointIndexDiagram a) (adjointIndexDiagram c) := rfl

theorem matrixDiagram_involutive : Function.Involutive (matrixDiagram R) := by
  intro A
  ext a c
  simp only [matrixDiagram_apply, adjointIndexDiagram_involutive a,
    adjointIndexDiagram_involutive c]

theorem matrixDiagram_raising (i : base.support) :
    matrixDiagram ℤ (raising pairing base i) = raising pairing base (baseDiagram i) := by
  ext a c
  have h := diagram_raising_entry (baseDiagram i) a c
  simpa only [baseDiagram_involutive i, matrixDiagram_apply] using h

theorem matrixDiagram_raising_pow (i : base.support) (n : ℕ) :
    matrixDiagram ℤ (raising pairing base i ^ n) = raising pairing base (baseDiagram i) ^ n := by
  calc
    _ = (matrixDiagram ℤ (raising pairing base i)) ^ n :=
      (matrixDiagram ℤ).map_pow _ n
    _ = _ := by rw [matrixDiagram_raising]

theorem matrixDiagram_dividedPower (i : base.support) (n : ℕ) :
    matrixDiagram ℤ (raisingDividedPower pairing base i n) =
      raisingDividedPower pairing base (baseDiagram i) n := by
  ext a c
  have h := congrArg (fun A : Matrix (base.support ⊕ Root) (base.support ⊕ Root) ℤ => A a c)
    (matrixDiagram_raising_pow i n)
  change (raising pairing base i ^ n) (adjointIndexDiagram a) (adjointIndexDiagram c) /
      (n.factorial : ℤ) = (raising pairing base (baseDiagram i) ^ n) a c / (n.factorial : ℤ)
  exact congrArg (fun z : ℤ => z / (n.factorial : ℤ)) h

theorem matrixDiagram_dividedOver (i : base.support) (n : ℕ) :
    matrixDiagram R (raisingDividedOver pairing base R i n) =
      raisingDividedOver pairing base R (baseDiagram i) n := by
  ext a c
  have h := congrArg (fun A : Matrix (base.support ⊕ Root) (base.support ⊕ Root) ℤ => A a c)
    (matrixDiagram_dividedPower i n)
  exact congrArg (Int.castRingHom R) h

theorem matrixDiagram_raisingExponential (i : base.support) (t : R) :
    matrixDiagram R (raisingExponential pairing base R i t) =
      raisingExponential pairing base R (baseDiagram i) t := by
  ext a c
  simp only [matrixDiagram_apply, raisingExponential, Matrix.sum_apply, Matrix.smul_apply]
  apply Finset.sum_congr rfl
  intro n hn
  have h := congrArg (fun A : Matrix (base.support ⊕ Root) (base.support ⊕ Root) R => A a c)
    (matrixDiagram_dividedOver R i n)
  exact congrArg (fun z : R => t ^ n • z) h

def unitsDiagram :
    (Matrix (base.support ⊕ Root) (base.support ⊕ Root) R)ˣ →*
      (Matrix (base.support ⊕ Root) (base.support ⊕ Root) R)ˣ :=
  Units.map (matrixDiagram R).toMonoidHom

theorem unitsDiagram_involutive : Function.Involutive (unitsDiagram R) := by
  intro A
  apply Units.ext
  exact matrixDiagram_involutive R A.val

theorem unitsDiagram_raising (i : base.support) (t : R) :
    unitsDiagram R (raisingRootElement pairing base R i t) =
      raisingRootElement pairing base R (baseDiagram i) t := by
  apply Units.ext
  exact matrixDiagram_raisingExponential R i t

theorem matrixDiagram_opposition :
    matrixDiagram R (oppositionOver pairing base R) = oppositionOver pairing base R := by
  classical
  ext a c
  cases a <;> cases c <;>
    simp only [matrixDiagram_apply, oppositionOver, RootPairing.GeckConstruction.ω,
      adjointIndexDiagram, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Matrix.map_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.of_apply,
      Matrix.one_apply, baseDiagram.injective.eq_iff, ← rootDiagram_neg,
      rootDiagram.injective.eq_iff] <;> first | rfl | (split <;> simp_all)

theorem unitsDiagram_opposition :
    unitsDiagram R (oppositionUnit pairing base R) = oppositionUnit pairing base R :=
  Units.ext (matrixDiagram_opposition R)

theorem unitsDiagram_lowering (i : base.support) (t : R) :
    unitsDiagram R (loweringRootElement pairing base R i t) =
      loweringRootElement pairing base R (baseDiagram i) t := by
  simp only [loweringRootElement, map_mul, map_inv, unitsDiagram_opposition,
    unitsDiagram_raising]

end Atlas.Chevalley.TwistedE6

import Atlas.LinearGroups.Chevalley.TwistedE6.DualOrbit
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! The diagram on the pair of actual minuscule matrix blocks. Its formulas
are integral and hold over any commutative coefficient ring. -/
noncomputable section
namespace Atlas.Chevalley.TwistedE6
open Classical E6Data Integral.Minuscule
variable (R : Type*) [CommRing R]

def dualMatrixDiagram (a : Option Unit) :
    Matrix (WeightOrbit pairing (dualOrbits (dualBlockSwap a)))
      (WeightOrbit pairing (dualOrbits (dualBlockSwap a))) R ≃+*
    Matrix (WeightOrbit pairing (dualOrbits a)) (WeightOrbit pairing (dualOrbits a)) R :=
  Matrix.reindexRingEquiv R (dualOrbitDiagram a).symm

@[simp] theorem dualMatrixDiagram_apply (a : Option Unit)
    (A : Matrix (WeightOrbit pairing (dualOrbits (dualBlockSwap a)))
      (WeightOrbit pairing (dualOrbits (dualBlockSwap a))) R)
    (μ ν : WeightOrbit pairing (dualOrbits a)) :
    dualMatrixDiagram R a A μ ν = A (dualOrbitDiagram a μ) (dualOrbitDiagram a ν) := rfl

def dualUnitsDiagram (a : Option Unit) :
    (Matrix (WeightOrbit pairing (dualOrbits (dualBlockSwap a)))
      (WeightOrbit pairing (dualOrbits (dualBlockSwap a))) R)ˣ →*
    (Matrix (WeightOrbit pairing (dualOrbits a)) (WeightOrbit pairing (dualOrbits a)) R)ˣ :=
  Units.map (dualMatrixDiagram R a).toMonoidHom

set_option maxHeartbeats 600000 in
theorem dualUnitsDiagram_root (a : Option Unit)
    (i : base.support) (ε : ℤ) (hε : ε ≠ 0) (t : R) :
    dualUnitsDiagram R a (weightOrbitRootElement pairing (dualOrbits (dualBlockSwap a))
      (dualOrbits_closed (dualBlockSwap a)) (dualOrbits_minuscule (dualBlockSwap a))
      R i.val ε hε t) =
    weightOrbitRootElement pairing (dualOrbits a) (dualOrbits_closed a)
      (dualOrbits_minuscule a) R (baseDiagram i).val ε hε t := by
  apply Units.ext
  ext μ ν
  change (weightOrbitRootElement pairing (dualOrbits (dualBlockSwap a))
      (dualOrbits_closed (dualBlockSwap a)) (dualOrbits_minuscule (dualBlockSwap a))
      R i.val ε hε t).val (dualOrbitDiagram a μ) (dualOrbitDiagram a ν) = _
  have hgrade : weightDiagram ν.val (corootElement pairing i.val) =
      ν.val (corootElement pairing (baseDiagram i).val) := by
    have h := weightDiagram_simple_grade ν.val (baseDiagram i)
    rw [baseDiagram_involutive i] at h
    exact h
  have hreflect : weightReflection pairing i.val (weightDiagram ν.val) =
      weightDiagram (weightReflection pairing (baseDiagram i).val ν.val) := by
    have h := weightDiagram_simple_reflection (baseDiagram i) ν.val
    rw [baseDiagram_involutive i] at h
    exact h.symm
  simp only [weightOrbitRootElement_entry, (dualOrbitDiagram a).injective.eq_iff,
    dualOrbitDiagram_val, hgrade, hreflect, weightDiagram.injective.eq_iff]

def dualBlocksDiagram :
    (∀ a, (Matrix (WeightOrbit pairing (dualOrbits a))
      (WeightOrbit pairing (dualOrbits a)) R)ˣ) →*
    (∀ a, (Matrix (WeightOrbit pairing (dualOrbits a))
      (WeightOrbit pairing (dualOrbits a)) R)ˣ) where
  toFun A a := dualUnitsDiagram R a (A (dualBlockSwap a))
  map_one' := funext fun a => map_one (dualUnitsDiagram R a)
  map_mul' _A _B := funext fun a => map_mul (dualUnitsDiagram R a) _ _

theorem dualBlocksDiagram_involutive : Function.Involutive (dualBlocksDiagram R) := by
  intro A
  funext a
  apply Units.ext
  ext μ ν
  cases a with
  | none =>
    change (A none).val
      ⟨weightDiagram (weightDiagram μ.val), _⟩
      ⟨weightDiagram (weightDiagram ν.val), _⟩ = (A none).val μ ν
    exact congrArg₂ (A none).val (Subtype.ext (weightDiagram_involutive μ.val))
      (Subtype.ext (weightDiagram_involutive ν.val))
  | some a =>
    cases a
    change (A (some ())).val
      ⟨weightDiagram (weightDiagram μ.val), _⟩
      ⟨weightDiagram (weightDiagram ν.val), _⟩ = (A (some ())).val μ ν
    exact congrArg₂ (A (some ())).val (Subtype.ext (weightDiagram_involutive μ.val))
      (Subtype.ext (weightDiagram_involutive ν.val))

end Atlas.Chevalley.TwistedE6

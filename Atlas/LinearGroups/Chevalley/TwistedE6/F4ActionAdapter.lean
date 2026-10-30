import Atlas.LinearGroups.Chevalley.TwistedE6.FixedSpaceAdapter
import Atlas.LinearGroups.Chevalley.RootData.F4
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionReducedWords
import Mathlib.Algebra.Module.Equiv.Basic

/-! Source-only structural continuation: the actual F4 root Weyl action has the
same four rational coordinate formulas as the actual folded E6 generators.

The coordinates use F4Data.baseIndexEquiv literally. The Cartan convention is
root first, coroot second, so reflection i uses column i. No reversal or
rescaling is needed. Only four coordinate cases are used, never a Weyl-group
enumeration. This file has not been compiled or audited by its author. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Atlas.Chevalley.TwistedE6.F4ActionAdapter

open Classical RootData FixedSpaceAdapter

section RationalAction

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Multiplication for the existing rational root-coordinate action, proved on
the actual simple-root basis. The codomain is the endomorphism monoid. -/
def rationalActionHom : P.weylGroupToPerm.range →* Module.End ℚ (b.support → ℚ) where
  toFun := rationalRootWeylLinear P b
  map_one' := by
    apply (Pi.basisFun ℚ b.support).ext
    intro i
    rw [← rationalRootCoordinates_simple_eq_basis P b i]
    change rationalRootWeylLinear P b 1 (rationalRootCoordinates P b i.val) =
      rationalRootCoordinates P b i.val
    exact rationalRootWeylLinear_root P b 1 i.val
  map_mul' w v := by
    apply (Pi.basisFun ℚ b.support).ext
    intro i
    rw [← rationalRootCoordinates_simple_eq_basis P b i]
    change rationalRootWeylLinear P b (w * v) (rationalRootCoordinates P b i.val) =
      rationalRootWeylLinear P b w
        (rationalRootWeylLinear P b v (rationalRootCoordinates P b i.val))
    simp only [rationalRootWeylLinear_root, Subgroup.coe_mul, Equiv.Perm.mul_apply]

theorem rationalActionHom_injective : Function.Injective (rationalActionHom P b) := by
  intro w v h
  apply Subtype.ext
  apply Equiv.ext
  intro β
  apply rationalRootCoordinates_injective P b
  have he := congrArg
    (fun T : Module.End ℚ (b.support → ℚ) => T (rationalRootCoordinates P b β)) h
  change rationalRootWeylLinear P b w (rationalRootCoordinates P b β) =
    rationalRootWeylLinear P b v (rationalRootCoordinates P b β) at he
  simpa only [rationalRootWeylLinear_root] using he

end RationalAction

abbrev FourSpace := Fin 4 → ℚ
abbrev F4Weyl := F4Data.pairing.weylGroupToPerm.range

/-- Actual F4 base-support coordinates, reindexed by its existing marking. -/
def f4Coordinates : (F4Data.base.support → ℚ) ≃ₗ[ℚ] FourSpace where
  toFun x i := x (F4Data.baseIndexEquiv i)
  invFun v j := v (F4Data.baseIndexEquiv.symm j)
  left_inv x := by
    funext j
    exact congrArg x (F4Data.baseIndexEquiv.apply_symm_apply j)
  right_inv v := by
    funext i
    exact congrArg v (F4Data.baseIndexEquiv.symm_apply_apply i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev f4RootVector (β : F4Data.Root) : FourSpace :=
  f4Coordinates (rationalRootCoordinates F4Data.pairing F4Data.base β)

theorem f4BaseIndex_root (i : Fin 4) :
    (F4Data.baseIndexEquiv i).val = F4Table.simpleIndex i := rfl

theorem f4RootVector_simple (i : Fin 4) :
    f4RootVector (F4Data.baseIndexEquiv i).val = (Pi.single i (1 : ℚ) : FourSpace) := by
  funext j
  change rationalRootCoordinates F4Data.pairing F4Data.base
    (F4Data.baseIndexEquiv i).val (F4Data.baseIndexEquiv j) =
      (Pi.single i (1 : ℚ) : FourSpace) j
  rw [rationalRootCoordinates_simple]
  simp only [Equiv.apply_eq_iff_eq, Pi.single_apply, eq_comm]

/-- These are the existing integral F4 simple coefficients, cast to Q. -/
theorem f4RootVector_coordinates (β : F4Data.Root) :
    f4RootVector β = fun i => (F4Table.coordinates β i : ℚ) := by
  have hs : F4Data.pairing.root β =
      ∑ i : Fin 4, F4Table.coordinates β i •
        F4Data.pairing.root (F4Data.baseIndexEquiv i).val := by
    change F4Table.coordinates β = ∑ i : Fin 4,
      F4Table.coordinates β i • F4Table.coordinates (F4Table.simpleIndex i)
    simp only [F4Table.simple_coordinates]
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite]
  have hc := rationalRootCoordinates_of_sum F4Data.pairing F4Data.base β
    (fun i : Fin 4 => (F4Data.baseIndexEquiv i).val) (F4Table.coordinates β) hs
  calc
    f4RootVector β = f4Coordinates
        (∑ i : Fin 4, (F4Table.coordinates β i : ℚ) •
          rationalRootCoordinates F4Data.pairing F4Data.base
            (F4Data.baseIndexEquiv i).val) := congrArg f4Coordinates hc
    _ = ∑ i : Fin 4, (F4Table.coordinates β i : ℚ) •
        (Pi.single i (1 : ℚ) : FourSpace) := by
      simp only [map_sum, map_smul, RingHom.id_apply]
      change (∑ i : Fin 4, (F4Table.coordinates β i : ℚ) •
        f4RootVector (F4Data.baseIndexEquiv i).val) = _
      simp only [f4RootVector_simple]
    _ = fun i => (F4Table.coordinates β i : ℚ) := by
      funext j
      simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite]

/-- The inherited rational F4 Weyl action, in its actual four marked coordinates. -/
def f4Action : F4Weyl →* Module.End ℚ FourSpace :=
  f4Coordinates.conjRingEquiv.toMonoidHom.comp
    (rationalActionHom F4Data.pairing F4Data.base)

theorem f4Action_apply (w : F4Weyl) (v : FourSpace) :
    f4Action w v = f4Coordinates
      (rationalRootWeylLinear F4Data.pairing F4Data.base w (f4Coordinates.symm v)) := rfl

theorem f4Action_root (w : F4Weyl) (β : F4Data.Root) :
    f4Action w (f4RootVector β) = f4RootVector (w.val β) := by
  rw [f4Action_apply]
  change f4Coordinates (rationalRootWeylLinear F4Data.pairing F4Data.base w
    (f4Coordinates.symm (f4Coordinates
      (rationalRootCoordinates F4Data.pairing F4Data.base β)))) = _
  rw [LinearEquiv.symm_apply_apply, rationalRootWeylLinear_root]

theorem f4Action_injective : Function.Injective f4Action := by
  intro w v h
  apply rationalActionHom_injective F4Data.pairing F4Data.base
  apply f4Coordinates.conjRingEquiv.injective
  exact h

def f4Simple (a : Fin 4) : F4Weyl :=
  simpleWeylReflection F4Data.pairing F4Data.base (F4Data.baseIndexEquiv a)

/-- Reflection in simple node a uses column a of the actual F4 Cartan matrix. -/
theorem f4Simple_coordinates (a : Fin 4) (β : F4Data.Root) :
    F4Table.coordinates ((f4Simple a).val β) =
      foldedReflection ℤ a (F4Table.coordinates β) := by
  change F4Table.coordinates
    (F4Table.reflectionIndex (F4Table.simpleIndex a) β) = _
  rw [F4Table.reflection_root, F4Table.simple_coordinates]
  have hd : F4Table.dualCoordinates (F4Table.simpleIndex a) =
      fun j => F4Table.cartan j a := funext (F4Table.simple_dual_coordinates a)
  rw [hd]
  funext j
  fin_cases a <;> fin_cases j <;>
    simp [F4Table.dot, F4Table.cartan, CartanMatrix.F₄, foldedReflection,
      Fin.sum_univ_succ, Pi.single_apply, smul_eq_mul] <;> ring

theorem foldedReflection_cast (a : Fin 4) (x : Fin 4 → ℤ) :
    (fun j => (foldedReflection ℤ a x j : ℚ)) =
      foldedReflection ℚ a (fun j => (x j : ℚ)) := by
  funext j
  fin_cases a <;> fin_cases j <;> simp [foldedReflection]

/-- Exact equality of the two actual generator actions, on all rational vectors. -/
theorem f4Action_simple (a : Fin 4) :
    f4Action (f4Simple a) = fourGenerator a := by
  apply (Pi.basisFun ℚ (Fin 4)).ext
  intro j
  rw [Pi.basisFun_apply, ← f4RootVector_simple j, f4Action_root, fourGenerator_apply,
    f4RootVector_coordinates, f4RootVector_coordinates, f4Simple_coordinates]
  exact foldedReflection_cast a (F4Table.coordinates (F4Data.baseIndexEquiv j).val)

theorem f4Action_simple_apply (a : Fin 4) (v : FourSpace) :
    f4Action (f4Simple a) v = foldedReflection ℚ a v := by
  rw [f4Action_simple, fourGenerator_apply]

end Atlas.Chevalley.TwistedE6.F4ActionAdapter

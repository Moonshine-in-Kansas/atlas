import Atlas.LinearGroups.F4.Basic
import Atlas.Algebra.Albert.UniversalCriterion
import Atlas.Algebra.Albert.ShortRootNaturality
import Atlas.Algebra.Albert.CoordinateCycle

noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

theorem shortRoot_universal_norm (i : Fin 8) (t : F) :
    Atlas.Albert.norm (Atlas.Albert.scalarExtension (Atlas.Albert.shortRootEquiv i t)
      MvPolynomial.C Atlas.Albert.universalVector) = Atlas.Albert.normPolynomial := by
  rw [Atlas.Albert.scalarExtension_eq _ _
    (Atlas.Albert.shortRootLinear i (MvPolynomial.C t))
    (Atlas.Albert.shortRootEquiv_map MvPolynomial.C i t)]
  exact Atlas.Albert.shortRootLinear_norm i _ _

/-- The eight short root groups for the first diagonal pair. -/
def shortRootFirstPair (i : Fin 8) (t : F) : Model F :=
  Atlas.Albert.ofUniversalNorm (Atlas.Albert.shortRootEquiv i t)
    (Atlas.Albert.shortRootEquiv_unit i t) (shortRoot_universal_norm i t)

theorem shortRootFirstPair_apply (i : Fin 8) (t : F) (x : Atlas.Albert.Carrier F) :
    (shortRootFirstPair i t).val x = Atlas.Albert.shortRootLinear i t x := rfl

theorem shortRootFirstPair_zero (i : Fin 8) : shortRootFirstPair (F := F) i 0 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact Atlas.Albert.shortRootLinear_zero i x

theorem shortRootFirstPair_add (i : Fin 8) (s t : F) :
    shortRootFirstPair i (s + t) = shortRootFirstPair i s * shortRootFirstPair i t := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact (Atlas.Albert.shortRootLinear_add i s t x).symm

theorem shortRootFirstPair_injective (i : Fin 8) :
    Function.Injective (shortRootFirstPair (F := F) i) := by
  intro s t h
  have hh := congrArg (fun g : Model F =>
    (g.val ((![1, 0, 0], 0) : Atlas.Albert.Carrier F)).2 2 i) h
  fin_cases i <;>
    simpa [Matrix.vecHead, Matrix.vecTail, shortRootFirstPair, Atlas.Albert.ofUniversalNorm, Atlas.Albert.shortRootEquiv,
    Atlas.Albert.shortRootLinear, Atlas.Albert.shortRootFormula,
    Atlas.SplitOctonion.basisVector, Atlas.SplitOctonion.trace, Atlas.SplitOctonion.mul,
    Atlas.SplitOctonion.conjugate, Atlas.SplitOctonion.unit] using hh

theorem coordinateCycle_universal_norm :
    Atlas.Albert.norm (Atlas.Albert.scalarExtension
      (Atlas.Albert.coordinateCycleEquiv (F := F)) MvPolynomial.C
      Atlas.Albert.universalVector) = Atlas.Albert.normPolynomial := by
  rw [Atlas.Albert.scalarExtension_eq _ _
    (Atlas.Albert.coordinateCycleEquiv.toLinearMap)
    (Atlas.Albert.coordinateCycle_map MvPolynomial.C)]
  exact Atlas.Albert.coordinateCycle_norm _

def coordinateCycle : Model F :=
  Atlas.Albert.ofUniversalNorm Atlas.Albert.coordinateCycleEquiv
    Atlas.Albert.coordinateCycle_unit coordinateCycle_universal_norm

theorem coordinateCycle_apply (x : Atlas.Albert.Carrier F) :
    (coordinateCycle (F := F)).val x = Atlas.Albert.coordinateCycle x := rfl

theorem coordinateCycle_cube : (coordinateCycle (F := F)) ^ 3 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change Atlas.Albert.coordinateCycle
    (Atlas.Albert.coordinateCycle (Atlas.Albert.coordinateCycle x)) = x
  exact Atlas.Albert.coordinateCycle_three x

/-- The three diagonal pairs, each with all eight marked octonion parameters. -/
def shortRoot (pair : Fin 3) (i : Fin 8) (t : F) : Model F :=
  coordinateCycle ^ pair.val * shortRootFirstPair i t * (coordinateCycle ^ pair.val)⁻¹

theorem shortRoot_zero (pair : Fin 3) (i : Fin 8) : shortRoot (F := F) pair i 0 = 1 := by
  simp [shortRoot, shortRootFirstPair_zero]

theorem shortRoot_add (pair : Fin 3) (i : Fin 8) (s t : F) :
    shortRoot pair i (s + t) = shortRoot pair i s * shortRoot pair i t := by
  simp [shortRoot, shortRootFirstPair_add, mul_assoc]

theorem shortRoot_injective (pair : Fin 3) (i : Fin 8) :
    Function.Injective (shortRoot (F := F) pair i) := by
  intro s t h
  apply shortRootFirstPair_injective i
  exact mul_left_cancel (mul_right_cancel h)

end Atlas.F4

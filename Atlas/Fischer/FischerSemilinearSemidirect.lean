import Atlas.Fischer.FullSemilinearGeneration
import Atlas.Fischer.SemilinearAlgebraFinite
import Atlas.Fischer.GeneratedAlgebraParity
import Atlas.GroupTheory.InvolutionSection
import Atlas.GroupTheory.KernelComplement
import Mathlib.GroupTheory.SemidirectProduct

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def rootReflectionComplement (t : ReflectingRootParameter) : Subgroup rootGeneratedAlgebraGroup :=
  Subgroup.zpowers (displayedAlgebraRootElement t)

theorem rootReflection_parity_restriction_bijective (t : ReflectingRootParameter) :
    Function.Bijective (rootGeneratedAlgebraParity.comp (rootReflectionComplement t).subtype) := by
  letI := semilinearAlgebraAutomorphism_finite
  apply Atlas.GroupTheory.involution_restriction_bijective rootGeneratedAlgebraParity
    (by simp [Nat.card_congr (Multiplicative.toAdd : Multiplicative Bit ≃ Bit),
      Nat.card_eq_fintype_card,Bit,ZMod.card])
    (displayedAlgebraRootElement t) (displayedAlgebraRootElement_mul_self t)
  rw [displayedAlgebraRootElement_parity]
  decide

theorem rootReflectionComplement_order (t : ReflectingRootParameter) :
    Nat.card (rootReflectionComplement t)=2 := by
  rw [Nat.card_congr (MulEquiv.ofBijective _ (rootReflection_parity_restriction_bijective t)).toEquiv]
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative Bit ≃ Bit)]
  simp [Nat.card_eq_fintype_card,Bit,ZMod.card]

theorem rootReflection_isComplement (t : ReflectingRootParameter) :
    rootGeneratedAlgebraParity.ker.IsComplement' (rootReflectionComplement t) :=
  Atlas.GroupTheory.isComplement_kernel_of_restriction_bijective
    rootGeneratedAlgebraParity (rootReflectionComplement t)
    (rootReflection_parity_restriction_bijective t)

/-- The actual root reflection acts by conjugation on the linear parity kernel. -/
def rootReflectionPositiveAction (t : ReflectingRootParameter) :
    rootReflectionComplement t →* MulAut rootGeneratedAlgebraParity.ker :=
  rootGeneratedAlgebraParity.ker.normalizerMonoidHom.comp
    (Subgroup.inclusion (rootGeneratedAlgebraParity.ker.normalizer_eq_top ▸ le_top))

def generatedAlgebraFullEquiv : rootGeneratedAlgebraGroup ≃* SemilinearAlgebraAutomorphism :=
  (MulEquiv.subgroupCongr rootGeneratedAlgebraGroup_eq_top).trans Subgroup.topEquiv

/-- The full actual semilinear algebra group is the semidirect product of its
faithfully represented linear triple cover with any chosen root reflection. -/
def fullSemilinearSemidirectEquiv (t : ReflectingRootParameter) :
    rootGeneratedAlgebraParity.ker ⋊[rootReflectionPositiveAction t]
      rootReflectionComplement t ≃* SemilinearAlgebraAutomorphism :=
  (SemidirectProduct.mulEquivSubgroup (rootReflection_isComplement t)).trans generatedAlgebraFullEquiv

theorem fullSemilinearSemidirectEquiv_apply (t : ReflectingRootParameter)
    (x : rootGeneratedAlgebraParity.ker ⋊[rootReflectionPositiveAction t] rootReflectionComplement t) :
    fullSemilinearSemidirectEquiv t x=x.left.val.val*x.right.val.val := rfl

end Atlas.Fischer

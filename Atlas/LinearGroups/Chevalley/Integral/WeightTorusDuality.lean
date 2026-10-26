import Atlas.LinearGroups.Chevalley.Integral.WeightTorusCharacters
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Module.Equiv.Basic

/-! Candidate. Actual coroot-parameter tuples are the characters of the full
integral weight lattice. No group-center identification is assumed. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) (b : P.Base) (R : Type*) [CommRing R]

def weightTorusCharacterHom (t : b.support → Rˣ) :
    Multiplicative (WeightLattice P) →* Rˣ where
  toFun μ := weightTorusCharacter P b R t μ.toAdd
  map_one' := by simp [weightTorusCharacter]
  map_mul' μ ν := by
    simp [weightTorusCharacter, zpow_add, Finset.prod_mul_distrib]

@[simp] theorem weightTorusCharacterHom_fundamental (t : b.support → Rˣ)
    (i : b.support) :
    weightTorusCharacterHom P b R t (Multiplicative.ofAdd (fundamentalWeights P b i)) = t i :=
  weightTorusCharacter_fundamental P b R t i

theorem weightCharacter_eq_of_fundamental
    (f g : Multiplicative (WeightLattice P) →* Rˣ)
    (h : ∀ i : b.support,
      f (Multiplicative.ofAdd (fundamentalWeights P b i)) =
      g (Multiplicative.ofAdd (fundamentalWeights P b i))) : f = g := by
  apply MonoidHom.toAdditiveRight.injective
  apply AddMonoidHom.toIntLinearMap_injective
  apply (fundamentalWeights P b).ext
  intro i
  exact congrArg Additive.ofMul (h i)

def weightTorusCharacterEquiv :
    (b.support → Rˣ) ≃* (Multiplicative (WeightLattice P) →* Rˣ) where
  toFun := weightTorusCharacterHom P b R
  invFun f i := f (Multiplicative.ofAdd (fundamentalWeights P b i))
  left_inv t := by funext i; exact weightTorusCharacterHom_fundamental P b R t i
  right_inv f := by
    apply weightCharacter_eq_of_fundamental P b R
    intro i
    exact weightTorusCharacterHom_fundamental P b R _ i
  map_mul' t s := by
    apply weightCharacter_eq_of_fundamental P b R
    intro i
    simp

end Atlas.Chevalley.Integral.Minuscule

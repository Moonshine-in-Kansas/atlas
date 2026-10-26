import Atlas.LinearGroups.Chevalley.Integral.WeightTorusDuality
import Atlas.LinearGroups.Chevalley.TorusHom
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The kernel of the actual adjoint torus parameter map is the
character group of P/Q. This does not identify the kernel of the full companion
projection with this torus subgroup. -/
noncomputable section
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) (R : Type*) [CommRing R]

def rootTrivialWeightCharacters :
    Subgroup (Multiplicative (WeightLattice P) →* Rˣ) where
  carrier := {f | ∀ a : ι, f (Multiplicative.ofAdd (rootWeight P a)) = 1}
  one_mem' := by intro a; rfl
  mul_mem' := by intro f g hf hg a; change f _ * g _ = 1; rw [hf a,hg a,one_mul]
  inv_mem' := by intro f hf a; change (f _)⁻¹ = 1; rw [hf a,inv_one]

def weightRootQuotientCharacterLift (f : rootTrivialWeightCharacters P R) :
    Multiplicative (WeightLattice P ⧸ rootLattice P) →* Rˣ :=
  ((rootLattice P).liftQ f.val.toAdditiveRight.toIntLinearMap (by
    change Submodule.span ℤ (Set.range (rootWeight P)) ≤ _
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    change Additive.ofMul (f.val (Multiplicative.ofAdd (rootWeight P a))) = 0
    exact congrArg Additive.ofMul (f.property a))).toAddMonoidHom.toMultiplicativeLeft

def weightRootQuotientCharacterPullback
    (f : Multiplicative (WeightLattice P ⧸ rootLattice P) →* Rˣ) :
    rootTrivialWeightCharacters P R :=
  ⟨f.comp ((rootLattice P).mkQ.toAddMonoidHom.toMultiplicative), by
    intro a
    have hz : (rootLattice P).mkQ (rootWeight P a) = 0 :=
      (Submodule.Quotient.mk_eq_zero (rootLattice P)).mpr (rootWeight_mem_rootLattice P a)
    change f (Multiplicative.ofAdd ((rootLattice P).mkQ (rootWeight P a))) = 1
    rw [hz]
    exact f.map_one⟩

def weightRootQuotientCharacterEquiv :
    (Multiplicative (WeightLattice P ⧸ rootLattice P) →* Rˣ) ≃*
      rootTrivialWeightCharacters P R where
  toFun := weightRootQuotientCharacterPullback P R
  invFun := weightRootQuotientCharacterLift P R
  left_inv f := by
    apply MonoidHom.ext
    intro x
    change weightRootQuotientCharacterLift P R
      (weightRootQuotientCharacterPullback P R f) (Multiplicative.ofAdd x.toAdd) =
      f (Multiplicative.ofAdd x.toAdd)
    refine Submodule.Quotient.induction_on (rootLattice P) x.toAdd ?_
    intro μ
    rfl
  right_inv f := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    rfl
  map_mul' f g := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    rfl

variable [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

theorem adjointTorusParameters_eq_one_iff_character (t : b.support → Rˣ) :
    adjointTorusParameters P b R t = 1 ↔
      ∀ a : ι, weightTorusCharacterHom P b R t (Multiplicative.ofAdd (rootWeight P a)) = 1 := by
  have hp (a : ι) (i : b.support) :
      (rootWeight P a) (corootBasis P b i) = P.pairingIn ℤ a i := by
    rw [← weightCoordinates_apply, rootWeight_coordinates]
    exact (P.algebraMap_pairingIn ℤ a i).symm
  change adjointTorusParameters P b R t = 1 ↔
    ∀ a : ι, weightTorusCharacter P b R t (rootWeight P a)=1
  simpa only [weightTorusCharacter, hp] using
    adjointTorusParameters_eq_one_iff P b R t

def adjointTorusKernelRootCharacterEquiv :
    (adjointTorusParameters P b R).ker ≃* rootTrivialWeightCharacters P R where
  toFun t := ⟨weightTorusCharacterEquiv P b R t.val,
    (adjointTorusParameters_eq_one_iff_character P R b t.val).mp t.property⟩
  invFun f := ⟨(weightTorusCharacterEquiv P b R).symm f.val, by
    apply (adjointTorusParameters_eq_one_iff_character P R b _).mpr
    have he := (weightTorusCharacterEquiv P b R).apply_symm_apply f.val
    intro a
    exact (congrArg (fun g => g (Multiplicative.ofAdd (rootWeight P a))) he).trans (f.property a)⟩
  left_inv t := Subtype.ext ((weightTorusCharacterEquiv P b R).symm_apply_apply t.val)
  right_inv f := Subtype.ext ((weightTorusCharacterEquiv P b R).apply_symm_apply f.val)
  map_mul' t s := Subtype.ext ((weightTorusCharacterEquiv P b R).map_mul t.val s.val)

def adjointTorusKernelCharacterEquiv :
    (adjointTorusParameters P b R).ker ≃*
      (Multiplicative (WeightLattice P ⧸ rootLattice P) →* Rˣ) :=
  (adjointTorusKernelRootCharacterEquiv P R b).trans
    (weightRootQuotientCharacterEquiv P R).symm

theorem adjointTorusKernel_card :
    Nat.card (adjointTorusParameters P b R).ker =
      Nat.card (Multiplicative (WeightLattice P ⧸ rootLattice P) →* Rˣ) :=
  Nat.card_congr (adjointTorusKernelCharacterEquiv P R b).toEquiv

end Atlas.Chevalley

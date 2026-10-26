import Atlas.LinearGroups.Chevalley.Integral.LocalDiamondCommutation
import Atlas.LinearGroups.Chevalley.Integral.Adjoint
import Mathlib.Algebra.Lie.Sl2

/-! UNCHECKED source candidate. Actual integral A2 Serre identities, derived
from the Geck sl2 triples and the compiled simple-diamond commutation.
This is not yet an exponential/group commutator or a perfectness proof. -/
noncomputable section
namespace Atlas.Chevalley.Integral
open RootPairing.GeckConstruction
attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)

include hdiamond

/-- The actual raising matrices satisfy the single-edge adjacent Serre
relation over Z. The Cartan orientation is row j, column i. -/
theorem raising_a2_serre (i j : b.support) (hij : i ≠ j)
    (hji : b.cartanMatrix j i = -1) :
    raising P b i * (raising P b i * raising P b j - raising P b j * raising P b i) -
      (raising P b i * raising P b j - raising P b j * raising P b i) * raising P b i = 0 := by
  let triple := (RootPairing.GeckConstruction.isSl2Triple (P := P) (b := b) i).symm
  have primitive : triple.HasPrimitiveVectorWith (raising P b j) (1 : ℤ) := by
    refine ⟨(RootPairing.GeckConstruction.isSl2Triple (P := P) (b := b) j).e_ne_zero,
      ?_, ?_⟩
    · change ⁅-RootPairing.GeckConstruction.h i, RootPairing.GeckConstruction.e j⁆ =
        (1 : ℤ) • RootPairing.GeckConstruction.e j
      rw [neg_lie, RootPairing.GeckConstruction.lie_h_e, hji]
      simp only [neg_one_smul, neg_neg, one_smul]
    · change lowering P b i * raising P b j - raising P b j * lowering P b i = 0
      exact sub_eq_zero.mpr
        (raising_lowering_commute_of_diamond P b hdiamond j i hij.symm).symm.eq
  have hz := primitive.pow_toEnd_f_eq_zero_of_eq_nat (n := 1) (by rfl)
  change (LieModule.toEnd ℤ
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
      (raising P b i) ^ (2 : ℕ)) (raising P b j) = 0 at hz
  simpa only [pow_two, Module.End.mul_apply, LieModule.toEnd_apply_apply,
    Ring.lie_def] using hz

/-- The actual integral composite bracket commutes with its first generator. -/
theorem raising_a2_commute_bracket_left (i j : b.support) (hij : i ≠ j)
    (hji : b.cartanMatrix j i = -1) :
    Commute (raising P b i)
      (raising P b i * raising P b j - raising P b j * raising P b i) :=
  sub_eq_zero.mp (raising_a2_serre P b hdiamond i j hij hji)

/-- The reverse Cartan entry -1 gives commutation with the second generator. -/
theorem raising_a2_commute_bracket_right (i j : b.support) (hij : i ≠ j)
    (hijc : b.cartanMatrix i j = -1) :
    Commute (raising P b j)
      (raising P b i * raising P b j - raising P b j * raising P b i) := by
  have h := (raising_a2_commute_bracket_left P b hdiamond j i hij.symm hijc).neg_right
  simpa only [neg_sub] using h

variable (R : Type*) [CommRing R]

/-- Integral derivation first, coefficient reduction afterward: no division
or characteristic restriction on the target ring. -/
theorem raisingOver_a2_commute_bracket (i j : b.support) (hij : i ≠ j)
    (hijc : b.cartanMatrix i j = -1) (hjic : b.cartanMatrix j i = -1) :
    Commute (raisingOver P b R i)
        (raisingOver P b R i * raisingOver P b R j - raisingOver P b R j * raisingOver P b R i) ∧
      Commute (raisingOver P b R j)
        (raisingOver P b R i * raisingOver P b R j - raisingOver P b R j * raisingOver P b R i) := by
  constructor
  · have h := congrArg (Int.castRingHom R).mapMatrix
      (raising_a2_commute_bracket_left P b hdiamond i j hij hjic).eq
    simp only [map_mul, map_sub] at h
    simpa only [raisingOver, RingHom.mapMatrix_apply, Commute, SemiconjBy] using h
  · have h := congrArg (Int.castRingHom R).mapMatrix
      (raising_a2_commute_bracket_right P b hdiamond i j hij hijc).eq
    simp only [map_mul, map_sub] at h
    simpa only [raisingOver, RingHom.mapMatrix_apply, Commute, SemiconjBy] using h

end Atlas.Chevalley.Integral

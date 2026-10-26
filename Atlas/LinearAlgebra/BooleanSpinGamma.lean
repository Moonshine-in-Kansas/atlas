import Atlas.LinearAlgebra.BooleanSpinOperators
import Mathlib.Tactic.Module

/-! The vector representation of the split odd quadratic space inside Boolean
spin endomorphisms. Only the vector map is asserted injective. All identities
are over an arbitrary commutative ring, including characteristic two. -/
noncomputable section
namespace Atlas.BooleanSpin
open Classical
open scoped BigOperators
variable {I : Type*} [Fintype I] [LinearOrder I]
variable (R : Type*) [CommRing R]

def axis (i : I) (x y : R) : Module.End R (Space (I := I) R) :=
  x • creation R i + y • annihilation R i

def gamma (x y : I → R) (z : R) : Module.End R (Space (I := I) R) :=
  (∑ i, axis R i (x i) (y i)) + z • parity R

theorem axis_square (i : I) (x y : R) :
    axis R i x y * axis R i x y = (x*y) • 1 := by
  calc
    _ = (x*y) • (creation R i * annihilation R i +
        annihilation R i * creation R i) := by
      simp only [axis, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
        smul_smul, step_square, smul_zero, zero_add, add_zero, smul_add]
      module
    _ = _ := by rw [creation_annihilation]

theorem axis_anticomm (i j : I) (hij : i ≠ j) (x y u v : R) :
    axis R i x y * axis R j u v + axis R j u v * axis R i x y = 0 := by
  have hcc := step_anticomm R j i (Ne.symm hij) true true
  have hca := step_anticomm R j i (Ne.symm hij) true false
  have hac := step_anticomm R j i (Ne.symm hij) false true
  have haa := step_anticomm R j i (Ne.symm hij) false false
  simp only [axis, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul,
    creation, annihilation, hcc, hca, hac, haa, smul_neg]
  module

theorem parity_axis (i : I) (x y : R) :
    parity R * axis R i x y + axis R i x y * parity R = 0 := by
  simp only [axis, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    creation, annihilation, parity_step, smul_neg]
  module

private theorem sum_axis_square (s : Finset I) (x y : I → R) :
    (∑ i ∈ s, axis R i (x i) (y i)) * (∑ i ∈ s, axis R i (x i) (y i)) =
      (∑ i ∈ s, x i*y i) • 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hc : axis R i (x i) (y i) * (∑ j ∈ s, axis R j (x j) (y j)) +
        (∑ j ∈ s, axis R j (x j) (y j)) * axis R i (x i) (y i) = 0 := by
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro j hj
      exact axis_anticomm R i j (by intro h; subst j; exact hi hj) _ _ _ _
    simp only [Finset.sum_insert hi]
    calc
      _ = axis R i (x i) (y i) * axis R i (x i) (y i) +
          (axis R i (x i) (y i) * (∑ j ∈ s, axis R j (x j) (y j)) +
          (∑ j ∈ s, axis R j (x j) (y j)) * axis R i (x i) (y i)) +
          (∑ j ∈ s, axis R j (x j) (y j)) * (∑ j ∈ s, axis R j (x j) (y j)) := by
        noncomm_ring
      _ = _ := by rw [hc, add_zero, axis_square, ih, add_smul]

theorem gamma_square (x y : I → R) (z : R) :
    gamma R x y z * gamma R x y z = ((∑ i, x i*y i) + z^2) • 1 := by
  let A := ∑ i, axis R i (x i) (y i)
  have hA : A*A = (∑ i, x i*y i) • 1 := sum_axis_square R Finset.univ x y
  have hc : parity R * A + A * parity R = 0 := by
    simp only [A, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => parity_axis R i (x i) (y i)
  change (A + z • parity R) * (A + z • parity R) = _
  calc
    _ = A*A + z • (parity R*A+A*parity R) +
        (z*z) • (parity (I := I) R*parity R) := by
      simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
      module
    _ = _ := by rw [hA, hc, smul_zero, add_zero, parity_square, pow_two, add_smul]

def vacuum : I → Bool := fun _ => false

def particle (i : I) : I → Bool := flip i (vacuum (I := I))

private theorem particle_ne_vacuum (i : I) : particle i ≠ vacuum := by
  intro h
  have := congrFun h i
  simp [particle, vacuum] at this

private theorem particle_injective : Function.Injective (particle (I := I)) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp [particle, vacuum, flip, hij] at this

private theorem flip_eq_vacuum (i : I) (σ : I → Bool) :
    flip i σ = vacuum ↔ σ = particle i := by
  constructor
  · intro h
    simpa only [particle, flip_flip] using congrArg (flip i) h
  · intro h
    rw [h]
    exact flip_flip i vacuum

private theorem creation_vacuum (i : I) :
    creation R i (Finsupp.single vacuum 1) = Finsupp.single (particle i) 1 := by
  simp [creation, step_single, vacuum, «prefix», signProduct, bitSign, particle]

private theorem annihilation_vacuum (i : I) :
    annihilation R i (Finsupp.single vacuum 1) = 0 := by
  simp [annihilation, step_single, vacuum]

private theorem axis_vacuum_vacuum (i : I) (x y : R) :
    axis R i x y (Finsupp.single vacuum 1) vacuum = 0 := by
  change (x • creation R i (Finsupp.single vacuum 1) +
    y • annihilation R i (Finsupp.single vacuum 1)) vacuum = 0
  rw [creation_vacuum, annihilation_vacuum]
  simp only [smul_zero, add_zero, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_eq_of_ne' (particle_ne_vacuum i), mul_zero]

private theorem axis_vacuum_particle (i j : I) (x y : R) :
    axis R j x y (Finsupp.single vacuum 1) (particle i) = if j=i then x else 0 := by
  change (x • creation R j (Finsupp.single vacuum 1) +
    y • annihilation R j (Finsupp.single vacuum 1)) (particle i) = _
  rw [creation_vacuum, annihilation_vacuum]
  simp only [smul_zero, add_zero, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply, particle_injective.eq_iff]
  split_ifs <;> simp only [mul_one, mul_zero]

private theorem axis_particle_vacuum (i j : I) (x y : R) :
    axis R j x y (Finsupp.single (particle i) 1) vacuum = if j=i then y else 0 := by
  by_cases hji : j=i
  · subst j
    have hi : particle i i = true := by simp [particle, vacuum]
    have hf : flip i (particle i) = vacuum := flip_flip i vacuum
    have hp : «prefix» R i (particle i) = 1 := by
      change «prefix» R i (flip i vacuum) = 1
      rw [prefix_flip_self]
      simp [«prefix», vacuum, signProduct, bitSign]
    simp [axis, creation, annihilation, step_single, hi, hf, hp]
  · have hp : particle i j = false := by simp [particle, flip, vacuum, hji]
    have hf : flip j (particle i) ≠ vacuum := by
      intro h
      exact hji (particle_injective ((flip_eq_vacuum j (particle i)).mp h)).symm
    simp [axis, creation, annihilation, step_single, hp, hji, hf,
      Finsupp.single_apply]

@[simp] theorem gamma_vacuum_vacuum (x y : I → R) (z : R) :
    gamma R x y z (Finsupp.single vacuum 1) vacuum = z := by
  simp [gamma, LinearMap.sum_apply, Finsupp.finsetSum_apply, axis_vacuum_vacuum,
    parity_single, vacuum, paritySign, signProduct, bitSign]

@[simp] theorem gamma_vacuum_particle (x y : I → R) (z : R) (i : I) :
    gamma R x y z (Finsupp.single vacuum 1) (particle i) = x i := by
  simp [gamma, LinearMap.sum_apply, Finsupp.finsetSum_apply, axis_vacuum_particle,
    parity_single, Finsupp.single_apply, particle_ne_vacuum, eq_comm]

@[simp] theorem gamma_particle_vacuum (x y : I → R) (z : R) (i : I) :
    gamma R x y z (Finsupp.single (particle i) 1) vacuum = y i := by
  simp [gamma, LinearMap.sum_apply, Finsupp.finsetSum_apply, axis_particle_vacuum,
    parity_single, Finsupp.single_apply, particle_ne_vacuum]

/-- Recover every coordinate without division, including the odd radical coordinate. -/
theorem gamma_injective : Function.Injective
    (fun v : (I → R) × (I → R) × R => gamma R v.1 v.2.1 v.2.2) := by
  intro v w h
  have hz := congrArg (fun f : Module.End R (Space (I := I) R) =>
    f (Finsupp.single vacuum 1) vacuum) h
  have hx (i : I) := congrArg (fun f : Module.End R (Space (I := I) R) =>
    f (Finsupp.single vacuum 1) (particle i)) h
  have hy (i : I) := congrArg (fun f : Module.End R (Space (I := I) R) =>
    f (Finsupp.single (particle i) 1) vacuum) h
  exact Prod.ext (funext fun i => by simpa using hx i)
    (Prod.ext (funext fun i => by simpa using hy i) (by simpa using hz))

/-- The polar radical line becomes scalar in characteristic two; gamma is still injective. -/
theorem gamma_radical_charTwo (h2 : (2 : R) = 0) (z : R) :
    gamma (I := I) R 0 0 z = z • 1 := by
  simp [gamma, axis, parity_eq_one_of_two_eq_zero R h2]

end Atlas.BooleanSpin

import Atlas.LinearGroups.Chevalley.AdjointOpposition
import Atlas.LinearGroups.Chevalley.A2WeylCommutator
import Mathlib.GroupTheory.IsPerfect

/-! A coefficient-one single-edge commutator makes the actual adjoint group
perfect whenever every simple node has a distinct single-edge neighbour. -/

noncomputable section
namespace Atlas.Chevalley
open Group Integral
open scoped commutatorElement

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R]

include hdiamond

/-- The commutator subgroup is normal, so the pinned A2 conjugate relation
puts the entire positive root subgroup at either end of a single edge inside it. -/
theorem adjointX_mem_commutator_of_a2_neighbour
    (i j : b.support) (hne : j ≠ i)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (t : R) :
    adjointX P b R i t ∈ commutator (Adjoint P b R) := by
  have hpin := adjointX_a2_commutator_eq_weyl_conjugate
    P b hdiamond R j i hne hji hij 1 t
  simp only [one_mul] at hpin
  have hc : adjointWeyl P b R j 1 * adjointX P b R i t *
      (adjointWeyl P b R j 1)⁻¹ ∈ commutator (Adjoint P b R) := by
    rw [← hpin]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hu : (adjointWeyl P b R j 1)⁻¹ *
      (adjointWeyl P b R j 1 * adjointX P b R i t) ∈
        commutator (Adjoint P b R) :=
    (inferInstance : (commutator (Adjoint P b R)).Normal).mem_comm hc
  simpa only [inv_mul_cancel_left] using hu

/-- The actual opposition automorphism sends positive generators to negative
ones and preserves their membership in the commutator subgroup. -/
theorem adjointY_mem_commutator_of_a2_neighbour
    (i j : b.support) (hne : j ≠ i)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (t : R) :
    adjointY P b R i t ∈ commutator (Adjoint P b R) := by
  let f := (adjointOppositionEquiv P b R).toMonoidHom
  have hx := adjointX_mem_commutator_of_a2_neighbour P b hdiamond R i j hne hij hji t
  have hm : f (adjointX P b R i t) ∈ (commutator (Adjoint P b R)).map f :=
    Subgroup.mem_map_of_mem f hx
  have hle : (commutator (Adjoint P b R)).map f ≤ commutator (Adjoint P b R) := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  have h := hle hm
  change adjointOppositionEquiv P b R (adjointX P b R i t) ∈
    commutator (Adjoint P b R) at h
  simpa only [adjointOppositionEquiv_X] using h

/-- Actual all-ring perfectness under an explicit single-edge-neighbour
condition on the actual Cartan matrix. No field or cardinality assumption occurs. -/
theorem adjoint_isPerfect_of_a2_neighbours
    (hrows : ∀ i : b.support, ∃ j : b.support, j ≠ i ∧
      b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -1) :
    IsPerfect (Adjoint P b R) := by
  apply isPerfect_def.mpr
  apply top_unique
  intro g hg
  apply adjoint_induction P b R ?_ ?_ (commutator _).one_mem
    (fun _ _ => (commutator _).mul_mem) (fun _ => (commutator _).inv_mem) g
  · intro i t
    obtain ⟨j, hne, hij, hji⟩ := hrows i
    exact adjointX_mem_commutator_of_a2_neighbour P b hdiamond R i j hne hij hji t
  · intro i t
    obtain ⟨j, hne, hij, hji⟩ := hrows i
    exact adjointY_mem_commutator_of_a2_neighbour P b hdiamond R i j hne hij hji t

end Atlas.Chevalley

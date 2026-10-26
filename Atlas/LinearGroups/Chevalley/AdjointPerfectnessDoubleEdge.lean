import Atlas.LinearGroups.Chevalley.AdjointPerfectnessA2
import Atlas.LinearGroups.Chevalley.B2WeylCommutator
import Atlas.GroupTheory.DoubleEdgeNormalPropagation

/-! Uncompiled source candidate. A2 seeds propagate over one directed
double edge by the actual integral commutator, including characteristic two. -/

noncomputable section
namespace Atlas.Chevalley
open Group Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R]

variable (hcover : ∀ i : b.support,
  (∃ j : b.support, j ≠ i ∧ b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -1) ∨
  (∃ j k : b.support, j ≠ i ∧ k ≠ j ∧
    b.cartanMatrix j k = -1 ∧ b.cartanMatrix k j = -1 ∧
    ((b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -2) ∨
     (b.cartanMatrix i j = -2 ∧ b.cartanMatrix j i = -1))))

include hdiamond hcover

/-- Positive simple-root generators are commutators when every node is on
a single edge, or joined by a double edge to a node on a single edge. -/
theorem adjointX_mem_commutator_of_a2_double_cover (i : b.support) (t : R) :
    adjointX P b R i t ∈ commutator (Adjoint P b R) := by
  rcases hcover i with ⟨j, hne, hij, hji⟩ | ⟨j, k, hji, hkj, hjk, hkj', hedge⟩
  · exact adjointX_mem_commutator_of_a2_neighbour P b hdiamond R i j hne hij hji t
  · have hj (s : R) : adjointX P b R j s ∈ commutator (Adjoint P b R) :=
      adjointX_mem_commutator_of_a2_neighbour P b hdiamond R j k hkj hjk hkj' s
    rcases hedge with ⟨hij, hji'⟩ | ⟨hij, hji'⟩
    · exact Atlas.GroupTheory.short_family_mem_normal_of_long_of_mixed_relation
        (commutator (Adjoint P b R)) (adjointX P b R i) (adjointX P b R j)
        (adjointWeyl P b R i 1) (adjointWeyl P b R j 1)
        (adjointX_b2_commutator_eq_weyl_product P b hdiamond R i j hji.symm hij hji') hj t
    · exact Atlas.GroupTheory.long_family_mem_normal_of_short_of_mixed_relation
        (commutator (Adjoint P b R)) (adjointX P b R j) (adjointX P b R i)
        (adjointWeyl P b R j 1) (adjointWeyl P b R i 1)
        (adjointX_b2_commutator_eq_weyl_product P b hdiamond R j i hji hji' hij) hj t

/-- All-ring perfectness under the explicit actual Cartan cover condition.
No field size, full projection-kernel or center statement is used. -/
theorem adjoint_isPerfect_of_a2_double_cover : IsPerfect (Adjoint P b R) := by
  have hx (i : b.support) (t : R) : adjointX P b R i t ∈ commutator (Adjoint P b R) :=
    adjointX_mem_commutator_of_a2_double_cover P b hdiamond R hcover i t
  have hy (i : b.support) (t : R) : adjointY P b R i t ∈ commutator (Adjoint P b R) := by
    let f := (adjointOppositionEquiv P b R).toMonoidHom
    have hm : f (adjointX P b R i t) ∈ (commutator (Adjoint P b R)).map f :=
      Subgroup.mem_map_of_mem f (hx i t)
    have hle : (commutator (Adjoint P b R)).map f ≤ commutator (Adjoint P b R) := by
      rw [map_commutator_eq]
      exact Subgroup.commutator_mono le_top le_top
    have h := hle hm
    change adjointOppositionEquiv P b R (adjointX P b R i t) ∈
      commutator (Adjoint P b R) at h
    simpa only [adjointOppositionEquiv_X] using h
  apply isPerfect_def.mpr
  apply top_unique
  intro g hg
  exact adjoint_induction P b R hx hy (commutator _).one_mem
    (fun _ _ => (commutator _).mul_mem) (fun _ => (commutator _).inv_mem) g

end Atlas.Chevalley

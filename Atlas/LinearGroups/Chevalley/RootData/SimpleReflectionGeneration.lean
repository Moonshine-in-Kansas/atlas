import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-! Simple reflections generate the full root-permutation Weyl image.
These are root-data statements, independent of the constructed linear groups.
Source candidate; compilation and dependency audits remain pending. -/

noncomputable section
namespace Atlas.Chevalley.RootData

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

theorem reflectionPerm_conjugate (i j : ι) :
    P.reflectionPerm (P.reflectionPerm j i) =
      P.reflectionPerm j * P.reflectionPerm i * P.reflectionPerm j := by
  ext k
  apply P.root.injective
  simp only [Equiv.Perm.mul_apply, P.root_reflectionPerm,
    P.reflection_reflectionPerm, LinearEquiv.mul_apply]

theorem reflectionPerm_opposite (i : ι) :
    P.reflectionPerm (P.reflectionPerm i i) = P.reflectionPerm i := by
  rw [reflectionPerm_conjugate]
  ext j
  simp only [Equiv.Perm.mul_apply, P.reflectionPerm_self]

theorem reflectionPerm_mem_simpleReflectionClosure (i : ι) :
    P.reflectionPerm i ∈
      Subgroup.closure (Set.range (fun j : b.support => P.reflectionPerm j.val)) := by
  let W := Subgroup.closure (Set.range (fun j : b.support => P.reflectionPerm j.val))
  change P.reflectionPerm i ∈ W
  apply b.induction_reflect i
  · intro j hj
    rwa [reflectionPerm_opposite]
  · intro j hj
    exact Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩
  · intro j k hj hk
    rw [reflectionPerm_conjugate]
    have hkW : P.reflectionPerm k ∈ W := Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩
    exact W.mul_mem (W.mul_mem hkW hj) hkW

theorem simpleReflectionClosure_eq_weylImage :
    Subgroup.closure (Set.range (fun j : b.support => P.reflectionPerm j.val)) =
      P.weylGroupToPerm.range := by
  rw [P.range_weylGroupToPerm]
  apply le_antisymm
  · apply Subgroup.closure_mono
    rintro w ⟨i, rfl⟩
    exact ⟨i.val, rfl⟩
  · rw [Subgroup.closure_le]
    rintro w ⟨i, rfl⟩
    exact reflectionPerm_mem_simpleReflectionClosure P b i

/-- Every actual root label is reached from a simple root by a word in the
simple reflection permutations. No group representation is assumed. -/
theorem exists_simpleRoot_word (i : ι) :
    ∃ j : b.support, ∃ w : Equiv.Perm ι,
      w ∈ Subgroup.closure (Set.range (fun k : b.support => P.reflectionPerm k.val)) ∧
        w j.val = i := by
  let W := Subgroup.closure (Set.range (fun k : b.support => P.reflectionPerm k.val))
  change ∃ j : b.support, ∃ w : Equiv.Perm ι, w ∈ W ∧ w j.val = i
  apply b.induction_reflect i
  · intro k hk
    obtain ⟨j, w, hw, hwi⟩ := hk
    refine ⟨j, P.reflectionPerm k * w,
      W.mul_mem (reflectionPerm_mem_simpleReflectionClosure P b k) hw, ?_⟩
    simpa only [Equiv.Perm.mul_apply, hwi]
  · intro j hj
    exact ⟨⟨j, hj⟩, 1, W.one_mem, rfl⟩
  · intro k l hk hl
    obtain ⟨j, w, hw, hwk⟩ := hk
    refine ⟨j, P.reflectionPerm l * w,
      W.mul_mem (Subgroup.subset_closure ⟨⟨l, hl⟩, rfl⟩) hw, ?_⟩
    simpa only [Equiv.Perm.mul_apply, hwk]

end Atlas.Chevalley.RootData

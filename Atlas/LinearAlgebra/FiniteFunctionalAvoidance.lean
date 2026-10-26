import Mathlib.Algebra.Module.Submodule.Union

/-! A single functional separates a finite vector list from a prescribed
subspace, over an infinite field. This is finite avoidance in the quotient. -/

noncomputable section
namespace Atlas.LinearAlgebra
open Classical

variable {K V ι : Type*} [Field K] [Infinite K]
  [AddCommGroup V] [Module K V] [Finite ι]

/-- A functional can vanish on a prescribed subspace and on exactly those
members of a finite vector family that lie in it. No dimension bound is needed. -/
theorem exists_linearFunctional_zero_iff_mem
    (S : Submodule K V) (v : ι → V) :
    ∃ f : V →ₗ[K] K, S ≤ LinearMap.ker f ∧
      ∀ i, f (v i) = 0 ↔ v i ∈ S := by
  let J := {i : ι // v i ∉ S}
  have hv : ∀ i : J, S.mkQ (v i.val) ≠ 0 := by
    intro i hi
    apply i.property
    simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hi
  obtain ⟨g, hg⟩ := Module.exists_dual_forall_apply_ne_zero (K := K)
    (fun i : J => S.mkQ (v i.val)) hv
  refine ⟨g.comp S.mkQ, ?_, ?_⟩
  · intro x hx
    change g (S.mkQ x) = 0
    have hx0 : S.mkQ x = 0 := by
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hx
    rw [hx0, map_zero]
  · intro i
    constructor
    · intro hi
      by_contra hnot
      exact hg ⟨i, hnot⟩ hi
    · intro hi
      change g (S.mkQ (v i)) = 0
      have hi0 : S.mkQ (v i) = 0 := by
        simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hi
      rw [hi0, map_zero]

end Atlas.LinearAlgebra

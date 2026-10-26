import Mathlib.LinearAlgebra.RootSystem.Irreducible
import Lean.Elab.Tactic.Omega

/-! Diagnostic for hypotheses on integral root pairings.
The root/coroot value 2 prevents the integral reflection representation
from being irreducible as a representation on all integer submodules. -/
namespace Atlas.Chevalley.Integral

theorem not_isIrreducible_over_int {ι M N : Type*}
    [AddCommGroup M] [AddCommGroup N] (P : RootPairing ι ℤ M N) (i : ι) :
    ¬ P.IsIrreducible := by
  intro hirr
  letI := hirr
  let f : M →ₗ[ℤ] M := (4 : ℤ) • LinearMap.id
  let S : Submodule ℤ M := LinearMap.range f
  have hinv : ∀ j, S ∈ Module.End.invtSubmodule (P.reflection j) := by
    intro j
    apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨P.reflection j y, by simp [f]⟩
  have hnzero : (4 : ℤ) • P.root i ≠ 0 := by
    intro h
    have he := congrArg (P.coroot' i) h
    have : (8 : ℤ) = 0 := by simpa using he
    omega
  have hne : S ≠ ⊥ := by
    intro he
    have hm : (4 : ℤ) • P.root i ∈ S := ⟨P.root i, rfl⟩
    rw [he, Submodule.mem_bot] at hm
    exact hnzero hm
  have htop : S = ⊤ :=
    RootPairing.IsIrreducible.eq_top_of_invtSubmodule_reflection S hinv hne
  have hm : P.root i ∈ S := htop.symm ▸ Submodule.mem_top
  obtain ⟨x, hx⟩ := hm
  have he := congrArg (P.coroot' i) hx
  have : (4 : ℤ) * P.coroot' i x = 2 := by simpa [f] using he
  omega

end Atlas.Chevalley.Integral

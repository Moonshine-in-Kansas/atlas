import F4Work.TailRhoRangeBounds

/-!
Source-only replacement candidate for the final two rho-normalizer proofs.
Both original theorem headers are preserved. The concrete proofs are now
applications of separately stated subgroup bounds and abstract group lemmas.
The earlier proofs, coordinate audit, staged sources and limits are untouched.
No Lean, Lake, audit, checker or memory measurement was run for this candidate.
-/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert Atlas.GroupTheory

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Actual rho conjugation preserves the q^10 tail, including m=0. -/
theorem rho_conjugate_mem_positiveRootTail {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) {g : Model F m}
    (hg : g ∈ positiveRootTailSubgroup hcard) :
    weylRhoModel m * g * (weylRhoModel m)⁻¹ ∈ positiveRootTailSubgroup hcard := by
  exact TailNormalizer.conjugate_mem_of_le_conj_comap
    (positiveRootTailSubgroup hcard) (weylRhoModel m)
    (positiveRootTail_le_rho_comap hcard) hg

theorem weylRhoModel_mem_tail_normalizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    weylRhoModel (F := F) m ∈ Subgroup.normalizer (positiveRootTailSubgroup hcard) := by
  exact TailNormalizer.mem_normalizer_of_inv_eq_self_of_conjugate_mem
    (positiveRootTailSubgroup hcard) (weylRhoModel m)
    (weylRhoModel_inv (F := F) m)
    (fun g hg => rho_conjugate_mem_positiveRootTail hcard hg)

end Atlas.ReeF4

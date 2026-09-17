import Atlas.Conway.MinimumTwentyThreeCycle
import Atlas.Conway.MinimumMonomialOrbits
import Atlas.GroupTheory.PrimeFreePermutation

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem minimum_point_cycle_invariant_card (a : Omega) :
    ∃ g : Mathieu24CodeModel, g.val a = a ∧ orderOf g.val = 23 ∧
      ∀ S : Set (LeechShell 4),
        (∀ x, shellRepresentation 4 (permutationEmbedding g) x ∈ S ↔ x ∈ S) →
        (∀ x ∈ S, integerDot (oddProfileBase {a} ∅) x.val.val = 0) →
        23 ∣ Nat.card S := by
  obtain ⟨g,ha,ho,hf⟩ := minimum_point_cycle_no_orthogonal_fixed_vector a
  refine ⟨g,ha,ho,?_⟩
  intro S hS horth
  let f := shellRepresentation 4 (permutationEmbedding g)
  let q : Equiv.Perm S := f.subtypePerm hS
  letI := Fintype.ofFinite S
  have hg : g ^ 23 = 1 := by
    apply Subtype.ext
    change g.val ^ 23 = 1
    rw [← ho,pow_orderOf_eq_one]
  have hp : f ^ 23 = 1 := by
    change (shellRepresentation 4 (permutationEmbedding g)) ^ 23 = 1
    rw [← map_pow,← map_pow,hg,map_one,map_one]
  have hq : q ^ 23 = 1 := by
    apply Equiv.ext
    intro x
    have he := congrArg (fun f : Equiv.Perm (LeechShell 4) => f x.val) hp
    apply Subtype.ext
    simpa only [q,Equiv.Perm.subtypePerm_pow,Equiv.Perm.subtypePerm_apply,Equiv.Perm.one_apply] using he
  have hfree : ∀ x : S, q x ≠ x := by
    intro x he
    have hh := congrArg (fun z : S => z.val.val.val) he
    exact hf x.val.val.val x.val.prop (horth x.val x.prop) hh
  rw [Nat.card_eq_fintype_card]
  exact Atlas.GroupTheory.prime_dvd_card_of_fixedPointFree q 23 (by decide) hq hfree

end Atlas.Conway

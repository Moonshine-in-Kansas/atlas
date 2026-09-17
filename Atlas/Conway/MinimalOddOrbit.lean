import Atlas.Conway.MonomialOrder
import Atlas.Lattices.LeechOddShells
import Atlas.Mathieu.SextetTransitivity

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def oddMinimumVector (a : Omega) (c : golay) : leech :=
  ⟨signedOddProfile {a} ∅ c,signedOddProfile_mem _ _ (by simp) c⟩

theorem permutation_odd_singleton (g : Mathieu24CodeModel) (a : Omega) :
    integerPermutation g.val (oddProfileBase {a} ∅) = oddProfileBase {g.val a} ∅ := by
  funext i
  change oddProfileBase {a} ∅ (g.val.symm i) = _
  simp only [oddProfileBase,Finset.mem_singleton,Finset.notMem_empty,ite_false,add_zero,
    Equiv.symm_apply_eq]

theorem monomial_odd_transport (g : Mathieu24CodeModel) (a : Omega) (c d : golay) :
    (monomialEmbedding ⟨Multiplicative.ofAdd (d + golayPermutationEquiv g c),g⟩).val
      (oddMinimumVector a c) = oddMinimumVector (g.val a) d := by
  apply Subtype.ext
  change signChange (d.val + coordinatePermutation g.val c.val)
    (integerPermutation g.val (signChange c.val (oddProfileBase {a} ∅))) = _
  rw [permutation_sign_conjugation,signChange_add,signChange_involutive,permutation_odd_singleton]
  rfl

theorem monomial_odd_minimum_transitive (a b : Omega) (c d : golay) :
    ∃ m : GolayMonomialGroup, (monomialEmbedding m).val (oddMinimumVector a c) =
      oddMinimumVector b d := by
  obtain ⟨g,hg⟩ := golay_coordinate_transitive a b
  refine ⟨⟨Multiplicative.ofAdd (d + golayPermutationEquiv g c),g⟩,?_⟩
  simpa [hg] using monomial_odd_transport g a c d

theorem odd_minimum_parameterization (x : leech) (hx : x.val ∈ oddNoFiveVectors 1) :
    ∃ a c, oddMinimumVector a c = x := by
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hx
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp p.1.prop
  refine ⟨a,p.2,?_⟩
  apply Subtype.ext
  change signedOddProfile {a} ∅ p.2 = x.val
  simpa [noFiveVector,ha] using hp

end Atlas.Conway

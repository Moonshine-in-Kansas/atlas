import Atlas.Fischer.ResidueRankThree
import Atlas.Fischer.ResidueNoncommutative
import Atlas.Fischer.ResidueOrderThreeWitness
import Atlas.GroupTheory.PrimitiveConjugateGenerators

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual nonempty centralizer residues are simple, without recognition. -/
theorem residueGroup_simple (S : Finset Omega) (hpos : 0<S.card) (hS : S.card≤2) :
    IsSimpleGroup (ResidueGroup S) := by
  haveI := residueGroup_nontrivial S hpos hS
  haveI := residueGroup_perfect S hpos hS
  haveI := residueGroup_faithful S hS
  haveI := residueGroup_primitive S hS
  obtain ⟨x,y,hxy⟩ := residue_exists_order_three_pair S hS
  exact Atlas.GroupTheory.simple_of_perfect_primitive_generators
    (residueDistinguishedElement S)
    (fun g x => (residueDistinguishedElement_covariance S g x).symm)
    (residueDistinguishedElement_generates S hS) x

end Atlas.Fischer

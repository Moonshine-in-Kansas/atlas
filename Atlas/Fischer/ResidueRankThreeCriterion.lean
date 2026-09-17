import Atlas.Fischer.ResidueCommutingSuborbit
import Atlas.Fischer.ResidueSubdegreeCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes MulAction

theorem residueSuborbits_transitive_of_noncommuting (S : Finset Omega) (hS : S.card ≤ 2)
    (i : Omega) (hi : i ∉ S)
    (hnon : ∀ x y : ResiduePoint S,
      ¬Commute (distinguishedRootElement (.inl i)) x.val →
      ¬Commute (distinguishedRootElement (.inl i)) y.val →
      ∃ g : residueCentralizer (insert i S), g.val*x.val*g.val⁻¹=y.val)
    (x y : ResiduePoint S) (hxy : residueSuborbitIndex S i hi x=residueSuborbitIndex S i hi y) :
    ∃ g : stabilizer (ResidueGroup S) (residueBasicPoint S i hi), g • x=y := by
  by_cases h0 : residueSuborbitIndex S i hi x=0
  · have hx := (residueSuborbitIndex_zero_iff S i hi x).mp h0
    have hy := (residueSuborbitIndex_zero_iff S i hi y).mp (hxy.symm.trans h0)
    exact ⟨1,by rw [one_smul,hx,hy]⟩
  by_cases h1 : residueSuborbitIndex S i hi x=1
  · exact residueCommutingSuborbit_transitive S (by omega) i hi x y h1 (hxy.symm.trans h1)
  have h2 : residueSuborbitIndex S i hi x=2 := by omega
  obtain ⟨g,hg⟩ := hnon x y ((residueSuborbitIndex_two_iff S i hi x).mp h2)
    ((residueSuborbitIndex_two_iff S i hi y).mp (hxy.symm.trans h2))
  exact ⟨residueAppendedStabilizerHom S i hi g,Subtype.ext hg⟩

theorem residue_primitive_of_noncommuting_transitive (S : Finset Omega) (hS : S.card ≤ 2)
    (i : Omega) (hi : i ∉ S)
    (hnon : ∀ x y : ResiduePoint S,
      ¬Commute (distinguishedRootElement (.inl i)) x.val →
      ¬Commute (distinguishedRootElement (.inl i)) y.val →
      ∃ g : residueCentralizer (insert i S), g.val*x.val*g.val⁻¹=y.val) :
    IsPreprimitive (ResidueGroup S) (ResiduePoint S) := by
  letI := residueGroup_transitive S (by omega)
  apply Atlas.GroupTheory.primitive_of_rankThree_nondivisibility
    (residueBasicPoint S i hi) (residueSuborbitIndex S i hi)
    (residueSuborbitIndex_base S i hi)
    (residueSuborbits_transitive_of_noncommuting S hS i hi hnon)
    (fischerRankThreeSubdegree ⟨S.card,by omega⟩)
    (fischerRankThree_singleton _) (residueSuborbit_card S hS i hi)
  · exact (residuePoint_rankThree_degree S hS).trans (fischerRankThree_degree_sum _)
  · rw [residuePoint_rankThree_degree S hS]
    exact fischerRankThree_first_nondivisibility _
  · rw [residuePoint_rankThree_degree S hS]
    exact fischerRankThree_second_nondivisibility _

end Atlas.Fischer

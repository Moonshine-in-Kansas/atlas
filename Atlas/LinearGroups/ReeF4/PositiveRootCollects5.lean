import Atlas.LinearGroups.ReeF4.PositiveRootFactorList
import Atlas.LinearGroups.ReeF4.AlternatingCollectionModel65
import Atlas.LinearGroups.ReeF4.AlternatingCollectionModel75
noncomputable section
namespace Atlas.ReeF4
open Atlas.GroupTheory
open scoped Pointwise
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option maxRecDepth 8192 in
theorem positiveRoot_collects_5 {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    CollectsBefore (alternatingLongRootHom hcard 2).range [(alternatingShortRootHom hcard 3).range, (alternatingLongRootHom hcard 3).range] := by
  intro x hx J hJ y hy
  rcases hx with ⟨p5,rfl⟩
  obtain ⟨u2,rfl⟩ := Multiplicative.ofAdd.surjective p5
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  rcases hJ with rfl | rfl
  ·
    rcases hy with ⟨p6,rfl⟩
    obtain ⟨⟨a3,b3⟩,rfl⟩ := (shortRootParameters m hcard).surjective p6
    refine ⟨positiveShortFactor hcard 3 (a3) (b3) * (1 * (1)), ?_, ?_⟩
    · exact ⟨positiveShortFactor hcard 3 (a3) (b3), ⟨shortRootParameters m hcard ((a3),(b3)),rfl⟩, 1 * (1), ⟨1, (alternatingLongRootHom hcard 3).range.one_mem, 1, (by simp [orderedSubgroupProduct]), rfl⟩, rfl⟩
    · simpa only [mul_one, one_mul, mul_assoc,positiveShortFactor,positiveLongFactor] using
        (alternatingCollection_65 hcard u2 a3 b3)
  ·
    rcases hy with ⟨p7,rfl⟩
    obtain ⟨u3,rfl⟩ := Multiplicative.ofAdd.surjective p7
    refine ⟨1 * (positiveLongFactor hcard 3 (u3) * (1)), ?_, ?_⟩
    · exact ⟨1, (alternatingShortRootHom hcard 3).range.one_mem, positiveLongFactor hcard 3 (u3) * (1), ⟨positiveLongFactor hcard 3 (u3), ⟨Multiplicative.ofAdd (u3),rfl⟩, 1, (by simp [orderedSubgroupProduct]), rfl⟩, rfl⟩
    · simpa only [mul_one, one_mul, mul_assoc,positiveShortFactor,positiveLongFactor] using
        (alternatingCollection_75 hcard u2 u3)
end Atlas.ReeF4

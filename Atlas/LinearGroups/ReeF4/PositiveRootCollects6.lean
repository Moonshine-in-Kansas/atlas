import Atlas.LinearGroups.ReeF4.PositiveRootFactorList
import Atlas.LinearGroups.ReeF4.AlternatingCollectionModel76
noncomputable section
namespace Atlas.ReeF4
open Atlas.GroupTheory
open scoped Pointwise
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option maxRecDepth 8192 in
theorem positiveRoot_collects_6 {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    CollectsBefore (alternatingShortRootHom hcard 3).range [(alternatingLongRootHom hcard 3).range] := by
  intro x hx J hJ y hy
  rcases hx with ⟨p6,rfl⟩
  obtain ⟨⟨a3,b3⟩,rfl⟩ := (shortRootParameters m hcard).surjective p6
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  subst J
  rcases hy with ⟨p7,rfl⟩
  obtain ⟨u3,rfl⟩ := Multiplicative.ofAdd.surjective p7
  refine ⟨positiveLongFactor hcard 3 (u3) * (1), ?_, ?_⟩
  · exact ⟨positiveLongFactor hcard 3 (u3), ⟨Multiplicative.ofAdd (u3),rfl⟩, 1, (by simp [orderedSubgroupProduct]), rfl⟩
  · simpa only [mul_one, one_mul, mul_assoc,positiveShortFactor,positiveLongFactor] using
      (alternatingCollection_76 hcard a3 b3 u3)
end Atlas.ReeF4

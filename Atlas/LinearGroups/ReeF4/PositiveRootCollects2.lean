import Atlas.LinearGroups.ReeF4.PositiveRootFactorList
import Atlas.LinearGroups.ReeF4.AlternatingCollectionModel32
import Atlas.LinearGroups.ReeF4.AlternatingCollectionModel42
import Atlas.LinearGroups.ReeF4.AlternatingCollectionModel52
import Atlas.LinearGroups.ReeF4.AlternatingCollectionModel62
import Atlas.LinearGroups.ReeF4.AlternatingCollectionModel72
noncomputable section
namespace Atlas.ReeF4
open Atlas.GroupTheory
open scoped Pointwise
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option maxRecDepth 8192 in
theorem positiveRoot_collects_2 {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    CollectsBefore (alternatingShortRootHom hcard 1).range [(alternatingLongRootHom hcard 1).range, (alternatingShortRootHom hcard 2).range, (alternatingLongRootHom hcard 2).range, (alternatingShortRootHom hcard 3).range, (alternatingLongRootHom hcard 3).range] := by
  intro x hx J hJ y hy
  rcases hx with ⟨p2,rfl⟩
  obtain ⟨⟨a1,b1⟩,rfl⟩ := (shortRootParameters m hcard).surjective p2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  rcases hJ with rfl | rfl | rfl | rfl | rfl
  ·
    rcases hy with ⟨p3,rfl⟩
    obtain ⟨u1,rfl⟩ := Multiplicative.ofAdd.surjective p3
    refine ⟨positiveLongFactor hcard 1 (u1) * (1 * (1 * (1 * (1 * (1))))), ?_, ?_⟩
    · exact ⟨positiveLongFactor hcard 1 (u1), ⟨Multiplicative.ofAdd (u1),rfl⟩, 1 * (1 * (1 * (1 * (1)))), ⟨1, (alternatingShortRootHom hcard 2).range.one_mem, 1 * (1 * (1 * (1))), ⟨1, (alternatingLongRootHom hcard 2).range.one_mem, 1 * (1 * (1)), ⟨1, (alternatingShortRootHom hcard 3).range.one_mem, 1 * (1), ⟨1, (alternatingLongRootHom hcard 3).range.one_mem, 1, (by simp [orderedSubgroupProduct]), rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    · simpa only [mul_one, one_mul, mul_assoc,positiveShortFactor,positiveLongFactor] using
        (alternatingCollection_32 hcard a1 b1 u1)
  ·
    rcases hy with ⟨p4,rfl⟩
    obtain ⟨⟨a2,b2⟩,rfl⟩ := (shortRootParameters m hcard).surjective p4
    refine ⟨positiveLongFactor hcard 1 (a1*a2) * (positiveShortFactor hcard 2 (a2) (b2) * (1 * (1 * (1 * (1))))), ?_, ?_⟩
    · exact ⟨positiveLongFactor hcard 1 (a1*a2), ⟨Multiplicative.ofAdd (a1*a2),rfl⟩, positiveShortFactor hcard 2 (a2) (b2) * (1 * (1 * (1 * (1)))), ⟨positiveShortFactor hcard 2 (a2) (b2), ⟨shortRootParameters m hcard ((a2),(b2)),rfl⟩, 1 * (1 * (1 * (1))), ⟨1, (alternatingLongRootHom hcard 2).range.one_mem, 1 * (1 * (1)), ⟨1, (alternatingShortRootHom hcard 3).range.one_mem, 1 * (1), ⟨1, (alternatingLongRootHom hcard 3).range.one_mem, 1, (by simp [orderedSubgroupProduct]), rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    · simpa only [mul_one, one_mul, mul_assoc,positiveShortFactor,positiveLongFactor] using
        (alternatingCollection_42 hcard a1 b1 a2 b2)
  ·
    rcases hy with ⟨p5,rfl⟩
    obtain ⟨u2,rfl⟩ := Multiplicative.ofAdd.surjective p5
    refine ⟨1 * (positiveShortFactor hcard 2 (0) (a1*u2) * (positiveLongFactor hcard 2 (u2) * (1 * (1 * (1))))), ?_, ?_⟩
    · exact ⟨1, (alternatingLongRootHom hcard 1).range.one_mem, positiveShortFactor hcard 2 (0) (a1*u2) * (positiveLongFactor hcard 2 (u2) * (1 * (1 * (1)))), ⟨positiveShortFactor hcard 2 (0) (a1*u2), ⟨shortRootParameters m hcard ((0),(a1*u2)),rfl⟩, positiveLongFactor hcard 2 (u2) * (1 * (1 * (1))), ⟨positiveLongFactor hcard 2 (u2), ⟨Multiplicative.ofAdd (u2),rfl⟩, 1 * (1 * (1)), ⟨1, (alternatingShortRootHom hcard 3).range.one_mem, 1 * (1), ⟨1, (alternatingLongRootHom hcard 3).range.one_mem, 1, (by simp [orderedSubgroupProduct]), rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    · simpa only [mul_one, one_mul, mul_assoc,positiveShortFactor,positiveLongFactor] using
        (alternatingCollection_52 hcard a1 b1 u2)
  ·
    rcases hy with ⟨p6,rfl⟩
    obtain ⟨⟨a3,b3⟩,rfl⟩ := (shortRootParameters m hcard).surjective p6
    refine ⟨1 * (1 * (1 * (positiveShortFactor hcard 3 (a3) (b3) * (1 * (1))))), ?_, ?_⟩
    · exact ⟨1, (alternatingLongRootHom hcard 1).range.one_mem, 1 * (1 * (positiveShortFactor hcard 3 (a3) (b3) * (1 * (1)))), ⟨1, (alternatingShortRootHom hcard 2).range.one_mem, 1 * (positiveShortFactor hcard 3 (a3) (b3) * (1 * (1))), ⟨1, (alternatingLongRootHom hcard 2).range.one_mem, positiveShortFactor hcard 3 (a3) (b3) * (1 * (1)), ⟨positiveShortFactor hcard 3 (a3) (b3), ⟨shortRootParameters m hcard ((a3),(b3)),rfl⟩, 1 * (1), ⟨1, (alternatingLongRootHom hcard 3).range.one_mem, 1, (by simp [orderedSubgroupProduct]), rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    · simpa only [mul_one, one_mul, mul_assoc,positiveShortFactor,positiveLongFactor] using
        (alternatingCollection_62 hcard a1 b1 a3 b3)
  ·
    rcases hy with ⟨p7,rfl⟩
    obtain ⟨u3,rfl⟩ := Multiplicative.ofAdd.surjective p7
    refine ⟨1 * (positiveShortFactor hcard 2 (0) (b1*u3) * (positiveLongFactor hcard 2 ((theta F m a1)*u3) * (positiveShortFactor hcard 3 (0) (a1*(theta F m u3)) * (positiveLongFactor hcard 3 (u3) * (1))))), ?_, ?_⟩
    · exact ⟨1, (alternatingLongRootHom hcard 1).range.one_mem, positiveShortFactor hcard 2 (0) (b1*u3) * (positiveLongFactor hcard 2 ((theta F m a1)*u3) * (positiveShortFactor hcard 3 (0) (a1*(theta F m u3)) * (positiveLongFactor hcard 3 (u3) * (1)))), ⟨positiveShortFactor hcard 2 (0) (b1*u3), ⟨shortRootParameters m hcard ((0),(b1*u3)),rfl⟩, positiveLongFactor hcard 2 ((theta F m a1)*u3) * (positiveShortFactor hcard 3 (0) (a1*(theta F m u3)) * (positiveLongFactor hcard 3 (u3) * (1))), ⟨positiveLongFactor hcard 2 ((theta F m a1)*u3), ⟨Multiplicative.ofAdd ((theta F m a1)*u3),rfl⟩, positiveShortFactor hcard 3 (0) (a1*(theta F m u3)) * (positiveLongFactor hcard 3 (u3) * (1)), ⟨positiveShortFactor hcard 3 (0) (a1*(theta F m u3)), ⟨shortRootParameters m hcard ((0),(a1*(theta F m u3))),rfl⟩, positiveLongFactor hcard 3 (u3) * (1), ⟨positiveLongFactor hcard 3 (u3), ⟨Multiplicative.ofAdd (u3),rfl⟩, 1, (by simp [orderedSubgroupProduct]), rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    · simpa only [mul_one, one_mul, mul_assoc,positiveShortFactor,positiveLongFactor] using
        (alternatingCollection_72 hcard a1 b1 u3)
end Atlas.ReeF4

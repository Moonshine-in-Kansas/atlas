import Atlas.LinearGroups.ReeF4.PositiveRootFactorList
import Atlas.LinearGroups.ReeF4.AlternatingCollectionModel21
import Atlas.LinearGroups.ReeF4.AlternatingCollectionModel31
import Atlas.LinearGroups.ReeF4.AlternatingCollectionModel41
import Atlas.LinearGroups.ReeF4.AlternatingCollectionModel51
import Atlas.LinearGroups.ReeF4.AlternatingCollectionModel61
import Atlas.LinearGroups.ReeF4.AlternatingCollectionModel71
noncomputable section
namespace Atlas.ReeF4
open Atlas.GroupTheory
open scoped Pointwise
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option maxRecDepth 8192 in
theorem positiveRoot_collects_1 {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    CollectsBefore (alternatingLongRootHom hcard 0).range [(alternatingShortRootHom hcard 1).range, (alternatingLongRootHom hcard 1).range, (alternatingShortRootHom hcard 2).range, (alternatingLongRootHom hcard 2).range, (alternatingShortRootHom hcard 3).range, (alternatingLongRootHom hcard 3).range] := by
  intro x hx J hJ y hy
  rcases hx with ⟨p1,rfl⟩
  obtain ⟨u0,rfl⟩ := Multiplicative.ofAdd.surjective p1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    rcases hy with ⟨p2,rfl⟩
    obtain ⟨⟨a1,b1⟩,rfl⟩ := (shortRootParameters m hcard).surjective p2
    refine ⟨positiveShortFactor hcard 1 (a1) (b1) * (1 * (1 * (1 * (1 * (1 * (1)))))), ?_, ?_⟩
    · exact ⟨positiveShortFactor hcard 1 (a1) (b1), ⟨shortRootParameters m hcard ((a1),(b1)),rfl⟩, 1 * (1 * (1 * (1 * (1 * (1))))), ⟨1, (alternatingLongRootHom hcard 1).range.one_mem, 1 * (1 * (1 * (1 * (1)))), ⟨1, (alternatingShortRootHom hcard 2).range.one_mem, 1 * (1 * (1 * (1))), ⟨1, (alternatingLongRootHom hcard 2).range.one_mem, 1 * (1 * (1)), ⟨1, (alternatingShortRootHom hcard 3).range.one_mem, 1 * (1), ⟨1, (alternatingLongRootHom hcard 3).range.one_mem, 1, (by simp [orderedSubgroupProduct]), rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    · simpa only [mul_one, one_mul, mul_assoc,positiveShortFactor,positiveLongFactor] using
        (alternatingCollection_21 hcard u0 a1 b1)
  ·
    rcases hy with ⟨p3,rfl⟩
    obtain ⟨u1,rfl⟩ := Multiplicative.ofAdd.surjective p3
    refine ⟨1 * (positiveLongFactor hcard 1 (u1) * (1 * (1 * (1 * (1 * (1)))))), ?_, ?_⟩
    · exact ⟨1, (alternatingShortRootHom hcard 1).range.one_mem, positiveLongFactor hcard 1 (u1) * (1 * (1 * (1 * (1 * (1))))), ⟨positiveLongFactor hcard 1 (u1), ⟨Multiplicative.ofAdd (u1),rfl⟩, 1 * (1 * (1 * (1 * (1)))), ⟨1, (alternatingShortRootHom hcard 2).range.one_mem, 1 * (1 * (1 * (1))), ⟨1, (alternatingLongRootHom hcard 2).range.one_mem, 1 * (1 * (1)), ⟨1, (alternatingShortRootHom hcard 3).range.one_mem, 1 * (1), ⟨1, (alternatingLongRootHom hcard 3).range.one_mem, 1, (by simp [orderedSubgroupProduct]), rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    · simpa only [mul_one, one_mul, mul_assoc,positiveShortFactor,positiveLongFactor] using
        (alternatingCollection_31 hcard u0 u1)
  ·
    rcases hy with ⟨p4,rfl⟩
    obtain ⟨⟨a2,b2⟩,rfl⟩ := (shortRootParameters m hcard).surjective p4
    refine ⟨positiveShortFactor hcard 1 (0) (a2*u0) * (1 * (positiveShortFactor hcard 2 (a2) (b2) * (1 * (1 * (1 * (1)))))), ?_, ?_⟩
    · exact ⟨positiveShortFactor hcard 1 (0) (a2*u0), ⟨shortRootParameters m hcard ((0),(a2*u0)),rfl⟩, 1 * (positiveShortFactor hcard 2 (a2) (b2) * (1 * (1 * (1 * (1))))), ⟨1, (alternatingLongRootHom hcard 1).range.one_mem, positiveShortFactor hcard 2 (a2) (b2) * (1 * (1 * (1 * (1)))), ⟨positiveShortFactor hcard 2 (a2) (b2), ⟨shortRootParameters m hcard ((a2),(b2)),rfl⟩, 1 * (1 * (1 * (1))), ⟨1, (alternatingLongRootHom hcard 2).range.one_mem, 1 * (1 * (1)), ⟨1, (alternatingShortRootHom hcard 3).range.one_mem, 1 * (1), ⟨1, (alternatingLongRootHom hcard 3).range.one_mem, 1, (by simp [orderedSubgroupProduct]), rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    · simpa only [mul_one, one_mul, mul_assoc,positiveShortFactor,positiveLongFactor] using
        (alternatingCollection_41 hcard u0 a2 b2)
  ·
    rcases hy with ⟨p5,rfl⟩
    obtain ⟨u2,rfl⟩ := Multiplicative.ofAdd.surjective p5
    refine ⟨1 * (1 * (1 * (positiveLongFactor hcard 2 (u2) * (1 * (1 * (1)))))), ?_, ?_⟩
    · exact ⟨1, (alternatingShortRootHom hcard 1).range.one_mem, 1 * (1 * (positiveLongFactor hcard 2 (u2) * (1 * (1 * (1))))), ⟨1, (alternatingLongRootHom hcard 1).range.one_mem, 1 * (positiveLongFactor hcard 2 (u2) * (1 * (1 * (1)))), ⟨1, (alternatingShortRootHom hcard 2).range.one_mem, positiveLongFactor hcard 2 (u2) * (1 * (1 * (1))), ⟨positiveLongFactor hcard 2 (u2), ⟨Multiplicative.ofAdd (u2),rfl⟩, 1 * (1 * (1)), ⟨1, (alternatingShortRootHom hcard 3).range.one_mem, 1 * (1), ⟨1, (alternatingLongRootHom hcard 3).range.one_mem, 1, (by simp [orderedSubgroupProduct]), rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    · simpa only [mul_one, one_mul, mul_assoc,positiveShortFactor,positiveLongFactor] using
        (alternatingCollection_51 hcard u0 u2)
  ·
    rcases hy with ⟨p6,rfl⟩
    obtain ⟨⟨a3,b3⟩,rfl⟩ := (shortRootParameters m hcard).surjective p6
    refine ⟨positiveShortFactor hcard 1 (0) (a3*(theta F m u0)) * (positiveLongFactor hcard 1 ((theta F m a3)*u0) * (positiveShortFactor hcard 2 (0) (b3*u0+a3*(theta F m a3)*u0) * (1 * (positiveShortFactor hcard 3 (a3) (b3) * (1 * (1)))))), ?_, ?_⟩
    · exact ⟨positiveShortFactor hcard 1 (0) (a3*(theta F m u0)), ⟨shortRootParameters m hcard ((0),(a3*(theta F m u0))),rfl⟩, positiveLongFactor hcard 1 ((theta F m a3)*u0) * (positiveShortFactor hcard 2 (0) (b3*u0+a3*(theta F m a3)*u0) * (1 * (positiveShortFactor hcard 3 (a3) (b3) * (1 * (1))))), ⟨positiveLongFactor hcard 1 ((theta F m a3)*u0), ⟨Multiplicative.ofAdd ((theta F m a3)*u0),rfl⟩, positiveShortFactor hcard 2 (0) (b3*u0+a3*(theta F m a3)*u0) * (1 * (positiveShortFactor hcard 3 (a3) (b3) * (1 * (1)))), ⟨positiveShortFactor hcard 2 (0) (b3*u0+a3*(theta F m a3)*u0), ⟨shortRootParameters m hcard ((0),(b3*u0+a3*(theta F m a3)*u0)),rfl⟩, 1 * (positiveShortFactor hcard 3 (a3) (b3) * (1 * (1))), ⟨1, (alternatingLongRootHom hcard 2).range.one_mem, positiveShortFactor hcard 3 (a3) (b3) * (1 * (1)), ⟨positiveShortFactor hcard 3 (a3) (b3), ⟨shortRootParameters m hcard ((a3),(b3)),rfl⟩, 1 * (1), ⟨1, (alternatingLongRootHom hcard 3).range.one_mem, 1, (by simp [orderedSubgroupProduct]), rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    · simpa only [mul_one, one_mul, mul_assoc,positiveShortFactor,positiveLongFactor] using
        (alternatingCollection_61 hcard u0 a3 b3)
  ·
    rcases hy with ⟨p7,rfl⟩
    obtain ⟨u3,rfl⟩ := Multiplicative.ofAdd.surjective p7
    refine ⟨1 * (positiveLongFactor hcard 1 (u3*(theta F m u0)) * (1 * (positiveLongFactor hcard 2 (u0*(theta F m u3)) * (1 * (positiveLongFactor hcard 3 (u3) * (1)))))), ?_, ?_⟩
    · exact ⟨1, (alternatingShortRootHom hcard 1).range.one_mem, positiveLongFactor hcard 1 (u3*(theta F m u0)) * (1 * (positiveLongFactor hcard 2 (u0*(theta F m u3)) * (1 * (positiveLongFactor hcard 3 (u3) * (1))))), ⟨positiveLongFactor hcard 1 (u3*(theta F m u0)), ⟨Multiplicative.ofAdd (u3*(theta F m u0)),rfl⟩, 1 * (positiveLongFactor hcard 2 (u0*(theta F m u3)) * (1 * (positiveLongFactor hcard 3 (u3) * (1)))), ⟨1, (alternatingShortRootHom hcard 2).range.one_mem, positiveLongFactor hcard 2 (u0*(theta F m u3)) * (1 * (positiveLongFactor hcard 3 (u3) * (1))), ⟨positiveLongFactor hcard 2 (u0*(theta F m u3)), ⟨Multiplicative.ofAdd (u0*(theta F m u3)),rfl⟩, 1 * (positiveLongFactor hcard 3 (u3) * (1)), ⟨1, (alternatingShortRootHom hcard 3).range.one_mem, positiveLongFactor hcard 3 (u3) * (1), ⟨positiveLongFactor hcard 3 (u3), ⟨Multiplicative.ofAdd (u3),rfl⟩, 1, (by simp [orderedSubgroupProduct]), rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    · simpa only [mul_one, one_mul, mul_assoc,positiveShortFactor,positiveLongFactor] using
        (alternatingCollection_71 hcard u0 u3)
end Atlas.ReeF4

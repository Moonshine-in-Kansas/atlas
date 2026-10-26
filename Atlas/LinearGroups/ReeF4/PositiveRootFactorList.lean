import Atlas.LinearGroups.ReeF4.PositiveRootFactors
import Atlas.LinearGroups.ReeF4.PositiveRootSubgroup
import Atlas.GroupTheory.OrderedSubgroupCollection

noncomputable section
namespace Atlas.ReeF4
open Atlas.GroupTheory
open scoped Pointwise
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def positiveRootFactorList {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) : List (Subgroup (Model F m)) :=
  [(alternatingShortRootHom hcard 0).range, (alternatingLongRootHom hcard 0).range,
   (alternatingShortRootHom hcard 1).range, (alternatingLongRootHom hcard 1).range,
   (alternatingShortRootHom hcard 2).range, (alternatingLongRootHom hcard 2).range,
   (alternatingShortRootHom hcard 3).range, (alternatingLongRootHom hcard 3).range]

theorem positiveRootWord_expand {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (u : Fin 4 → F) (v : Fin 4 → F × F) :
    alternatingRootWord hcard u v =
    positiveShortFactor hcard 0 (v 0).1 (v 0).2 *
    (positiveLongFactor hcard 0 (u 0) *
    (positiveShortFactor hcard 1 (v 1).1 (v 1).2 *
    (positiveLongFactor hcard 1 (u 1) *
    (positiveShortFactor hcard 2 (v 2).1 (v 2).2 *
    (positiveLongFactor hcard 2 (u 2) *
    (positiveShortFactor hcard 3 (v 3).1 (v 3).2 * positiveLongFactor hcard 3 (u 3))))))) := by
  unfold alternatingRootWord
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

theorem positiveRootFactorList_join {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    subgroupListJoin (positiveRootFactorList hcard) = positiveRootSubgroup hcard := by
  apply le_antisymm
  · apply (subgroupListJoin_le_iff _ _).mpr
    intro H hH
    simp only [positiveRootFactorList, List.mem_cons, List.not_mem_nil, or_false] at hH
    rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      rintro g ⟨u,rfl⟩
      first
      | exact alternatingShortRoot_mem_positiveRootSubgroup hcard _ u
      | exact alternatingLongRoot_mem_positiveRootSubgroup hcard _ u
  · apply (Subgroup.closure_le _).mpr
    rintro g (⟨k,u,rfl⟩ | ⟨k,u,rfl⟩)
    · apply ((subgroupListJoin_le_iff (positiveRootFactorList hcard) _).mp le_rfl)
        (alternatingShortRootHom hcard k).range (by fin_cases k <;> simp [positiveRootFactorList])
      exact ⟨u,rfl⟩
    · apply ((subgroupListJoin_le_iff (positiveRootFactorList hcard) _).mp le_rfl)
        (alternatingLongRootHom hcard k).range (by fin_cases k <;> simp [positiveRootFactorList])
      exact ⟨u,rfl⟩

theorem alternatingRootWord_range_eq_orderedProduct {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    Set.range (fun p : (Fin 4 → F) × (Fin 4 → F × F) => alternatingRootWord hcard p.1 p.2) =
      orderedSubgroupProduct (positiveRootFactorList hcard) := by
  ext g
  constructor
  · rintro ⟨⟨u,v⟩,rfl⟩
    dsimp only
    rw [positiveRootWord_expand]
    exact ⟨_,⟨shortRootParameters _ _ (v 0),rfl⟩,_,
      ⟨_,⟨Multiplicative.ofAdd (u 0),rfl⟩,_,
      ⟨_,⟨shortRootParameters _ _ (v 1),rfl⟩,_,
      ⟨_,⟨Multiplicative.ofAdd (u 1),rfl⟩,_,
      ⟨_,⟨shortRootParameters _ _ (v 2),rfl⟩,_,
      ⟨_,⟨Multiplicative.ofAdd (u 2),rfl⟩,_,
      ⟨_,⟨shortRootParameters _ _ (v 3),rfl⟩,_,
      ⟨_,⟨Multiplicative.ofAdd (u 3),rfl⟩,1,by simp [orderedSubgroupProduct],by simp⟩,
      rfl⟩,rfl⟩,rfl⟩,rfl⟩,rfl⟩,rfl⟩,rfl⟩
  · rintro ⟨s0,⟨x0,rfl⟩,g1,⟨l0,⟨y0,rfl⟩,g2,
      ⟨s1,⟨x1,rfl⟩,g3,⟨l1,⟨y1,rfl⟩,g4,
      ⟨s2,⟨x2,rfl⟩,g5,⟨l2,⟨y2,rfl⟩,g6,
      ⟨s3,⟨x3,rfl⟩,g7,⟨l3,⟨y3,rfl⟩,g8,h8,rfl⟩,rfl⟩,
      rfl⟩,rfl⟩,rfl⟩,rfl⟩,rfl⟩,rfl⟩
    have h8' : g8 = 1 := h8
    subst g8
    obtain ⟨p0,rfl⟩ := (shortRootParameters _ hcard).surjective x0
    obtain ⟨p1,rfl⟩ := (shortRootParameters _ hcard).surjective x1
    obtain ⟨p2,rfl⟩ := (shortRootParameters _ hcard).surjective x2
    obtain ⟨p3,rfl⟩ := (shortRootParameters _ hcard).surjective x3
    refine ⟨(![y0.toAdd,y1.toAdd,y2.toAdd,y3.toAdd],![p0,p1,p2,p3]),?_⟩
    dsimp only
    rw [positiveRootWord_expand]
    simp only [mul_one]
    rfl

end Atlas.ReeF4

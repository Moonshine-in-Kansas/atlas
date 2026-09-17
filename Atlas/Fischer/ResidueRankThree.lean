import Atlas.Fischer.ResidueRankThreeCriterion
import Atlas.Fischer.ResidueSuborbitInvariance
import Atlas.Fischer.ResidueNoncommutingOrbit

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes MulAction

theorem residueSuborbits_transitive (S : Finset Omega) (hS : S.card ≤ 2)
    (i : Omega) (hi : i ∉ S) (x y : ResiduePoint S)
    (hxy : residueSuborbitIndex S i hi x=residueSuborbitIndex S i hi y) :
    ∃ g : stabilizer (ResidueGroup S) (residueBasicPoint S i hi), g • x=y :=
  residueSuborbits_transitive_of_noncommuting S hS i hi
    (residue_noncommuting_transitive S hS i) x y hxy

theorem residueSuborbitIndex_surjective (S : Finset Omega) (hS : S.card ≤ 2)
    (i : Omega) (hi : i ∉ S) : Function.Surjective (residueSuborbitIndex S i hi) := by
  intro j
  have hp : ∀ s j : Fin 3,0<fischerRankThreeSubdegree s j := by
    intro s j
    fin_cases s <;> fin_cases j <;> decide
  have hc : 0<Nat.card {x : ResiduePoint S // residueSuborbitIndex S i hi x=j} := by
    rw [residueSuborbit_card S hS i hi]
    exact hp _ j
  obtain ⟨x⟩ := (Nat.card_pos_iff.mp hc).1
  exact ⟨x.val,x.property⟩

/-- The full stabilizer has exactly the three proved original-point orbits. -/
def residueSuborbitEquiv (S : Finset Omega) (hS : S.card ≤ 2)
    (i : Omega) (hi : i ∉ S) :
    orbitRel.Quotient (stabilizer (ResidueGroup S) (residueBasicPoint S i hi))
      (ResiduePoint S) ≃ Fin 3 :=
  (show orbitRel.Quotient (stabilizer (ResidueGroup S) (residueBasicPoint S i hi))
      (ResiduePoint S) ≃ Quotient (Setoid.ker (residueSuborbitIndex S i hi)) from
    Quotient.congrRight (fun x y => by
      change orbitRel (stabilizer (ResidueGroup S) (residueBasicPoint S i hi))
        (ResiduePoint S) x y ↔ residueSuborbitIndex S i hi x=residueSuborbitIndex S i hi y
      rw [orbitRel_apply]
      constructor
      · rintro ⟨g,rfl⟩
        exact residueSuborbitIndex_invariant S i hi g y
      · intro h
        exact residueSuborbits_transitive S hS i hi y x h.symm)).trans
    (Setoid.quotientKerEquivOfSurjective _ (residueSuborbitIndex_surjective S hS i hi))

theorem residueGroup_rank_three (S : Finset Omega) (hS : S.card ≤ 2)
    (i : Omega) (hi : i ∉ S) :
    Nat.card (orbitRel.Quotient (stabilizer (ResidueGroup S) (residueBasicPoint S i hi))
      (ResiduePoint S))=3 := by
  rw [Nat.card_congr (residueSuborbitEquiv S hS i hi),Nat.card_fin]

/-- Primitivity follows from the proved full suborbits and their exact block
divisibility obstruction. -/
theorem residueGroup_primitive (S : Finset Omega) (hS : S.card ≤ 2) :
    IsPreprimitive (ResidueGroup S) (ResiduePoint S) := by
  classical
  have hn : S.card<(Finset.univ : Finset Omega).card := by
    change S.card<24
    omega
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hn
  exact residue_primitive_of_noncommuting_transitive S hS i hi
    (residue_noncommuting_transitive S hS i)

end Atlas.Fischer

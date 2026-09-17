import Atlas.Fischer.ResidueSuborbitPartition
import Atlas.Fischer.ResiduePrimitivityArithmetic
import Mathlib.Tactic.IntervalCases

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

instance residuePointFinite (S : Finset Omega) : Finite (ResiduePoint S) :=
  Finite.of_injective (fun x : ResiduePoint S => x.val) Subtype.val_injective

theorem residuePoint_rankThree_degree (S : Finset Omega) (hS : S.card ≤ 2) :
    Nat.card (ResiduePoint S)=fischerRankThreeDegree ⟨S.card,by omega⟩ := by
  have hc := residuePoint_card S (by omega : S.card ≤ 5)
  have hs : S.card=0 ∨ S.card=1 ∨ S.card=2 := by omega
  rcases hs with hs | hs | hs <;> simpa [hs,fischerRankThreeDegree] using hc

theorem residueSuborbit_zero_card (S : Finset Omega) (i : Omega) (hi : i ∉ S) :
    Nat.card {x : ResiduePoint S // residueSuborbitIndex S i hi x=0}=1 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (residueSuborbitIndex_zero_iff S i hi))]
  simp

theorem residueSuborbit_one_card (S : Finset Omega) (hS : S.card ≤ 2)
    (i : Omega) (hi : i ∉ S) :
    Nat.card {x : ResiduePoint S // residueSuborbitIndex S i hi x=1}=
      fischerRankThreeSubdegree ⟨S.card,by omega⟩ 1 := by
  rw [Nat.card_congr (residueCommutingFiberEquiv S i hi)]
  have hSi : (insert i S).card=S.card+1 := Finset.card_insert_of_notMem hi
  have hc := residuePoint_card (insert i S) (by omega : (insert i S).card ≤ 5)
  have hs : S.card=0 ∨ S.card=1 ∨ S.card=2 := by omega
  rcases hs with hs | hs | hs <;> simpa [hSi,hs,fischerRankThreeSubdegree] using hc

/-- Exact sizes of all three literal classes. Transitivity within the last
class is an independent geometric obligation. -/
theorem residueSuborbit_card (S : Finset Omega) (hS : S.card ≤ 2)
    (i : Omega) (hi : i ∉ S) (j : Fin 3) :
    Nat.card {x : ResiduePoint S // residueSuborbitIndex S i hi x=j}=
      fischerRankThreeSubdegree ⟨S.card,by omega⟩ j := by
  have h0 := residueSuborbit_zero_card S i hi
  have h1 := residueSuborbit_one_card S hS i hi
  fin_cases j
  · exact h0.trans (fischerRankThree_singleton _).symm
  · exact h1
  · change Nat.card {x : ResiduePoint S // residueSuborbitIndex S i hi x=2}=
      fischerRankThreeSubdegree ⟨S.card,by omega⟩ 2
    letI : ∀ k : Fin 3,Finite {x : ResiduePoint S // residueSuborbitIndex S i hi x=k} :=
      fun _ => inferInstance
    have ht : Nat.card (ResiduePoint S)=
        ∑ k : Fin 3,Nat.card {x : ResiduePoint S // residueSuborbitIndex S i hi x=k} := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (residueSuborbitIndex S i hi)),Nat.card_sigma]
    rw [Fin.sum_univ_three,h0,h1,residuePoint_rankThree_degree S hS,
      fischerRankThree_degree_sum] at ht
    omega

end Atlas.Fischer

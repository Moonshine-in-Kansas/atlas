import Atlas.Algebra.Albert.ConePartition
import Atlas.Algebra.Albert.ConeArithmetic
import Atlas.Algebra.Albert.ZeroDiagonalLocus
import Atlas.Algebra.Albert.RankOneChartCount

/-! Independent count of the actual Albert rank-one cone. -/
noncomputable section
namespace Atlas.Albert
variable {F : Type*} [Field F] [Finite F]

theorem card_adjoint_zero :
    Nat.card {x : Carrier F // adjoint x=0} =
      1+(Nat.card F^9-1)*(Nat.card F^8+Nat.card F^4+1) := by
  rw [card_adjoint_zero_partition,card_rankOne_first_diagonal,
    Nat.card_congr (secondDiagonalEquiv (F:=F)),card_chart_third_zero,
    Nat.card_congr (thirdDiagonalEquiv (F:=F)),card_chart_two_zero,
    ZeroDiagonal.card_locus]
  exact rankOne_count_polynomial _ (by have := Finite.one_lt_card (α:=F); omega)

theorem card_rankOne_vectors :
    Nat.card {x : Carrier F // IsRankOne x} =
      (Nat.card F^9-1)*(Nat.card F^8+Nat.card F^4+1) := by
  classical
  letI := Fintype.ofFinite F
  have h0 : adjoint (0 : Carrier F)=0 := by
    simpa using adjoint_smul (0 : F) (unit : Carrier F)
  letI : Unique {x : {v : Carrier F // adjoint v=0} // x.val=0} :=
    { default := ⟨⟨0,h0⟩,rfl⟩
      uniq := fun x => Subtype.ext (Subtype.ext x.prop) }
  have hz : Fintype.card {x : {v : Carrier F // adjoint v=0} // x.val=0} = 1 :=
    Fintype.card_unique
  let e : {x : Carrier F // IsRankOne x} ≃
      {x : {v : Carrier F // adjoint v=0} // x.val≠0} :=
    (Equiv.subtypeEquivRight (fun x => and_comm)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun x : Carrier F => adjoint x=0)
        (fun x => x≠0)).symm
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,hz,
    ←Nat.card_eq_fintype_card,card_adjoint_zero]
  omega

end Atlas.Albert

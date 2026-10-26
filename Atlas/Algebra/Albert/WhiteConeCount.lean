import Atlas.Algebra.Albert.ConeCount
import Atlas.Algebra.Albert.WhiteZeroChartCount

namespace Atlas.Albert
variable {F : Type*} [Field F] [Finite F]

theorem card_white_cone_partition :
    Nat.card {x : Carrier F // adjoint x=0 ∧ trace x=0} =
      Nat.card {x : Carrier F // adjoint x=0 ∧ x.1 0≠0 ∧ trace x=0} +
      Nat.card {x : Carrier F // adjoint x=0 ∧ x.1 0=0 ∧ x.1 1≠0 ∧ trace x=0} +
      Nat.card {x : Carrier F // x.1=0 ∧ adjoint x=0} := by
  have h1 := Atlas.card_predicate_split (fun x : Carrier F => adjoint x=0 ∧ trace x=0)
    (fun x => x.1 0=0)
  have h2 := Atlas.card_predicate_split
    (fun x : Carrier F => (adjoint x=0 ∧ trace x=0) ∧ x.1 0=0) (fun x => x.1 1=0)
  have hz : Nat.card {x : Carrier F // ((adjoint x=0 ∧ trace x=0) ∧ x.1 0=0) ∧ x.1 1=0} =
      Nat.card {x : Carrier F // x.1=0 ∧ adjoint x=0} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    constructor
    · rintro ⟨⟨⟨ha,ht⟩,h0⟩,h1⟩
      refine ⟨?_,ha⟩
      funext i
      fin_cases i
      · exact h0
      · exact h1
      · simpa [trace,h0,h1] using ht
    · rintro ⟨hd,ha⟩
      simp [ha,hd,trace]
  rw [hz] at h2
  simp only [and_assoc,and_left_comm,and_comm,ne_eq] at h1 h2 ⊢
  omega

theorem card_white_cone :
    Nat.card {x : Carrier F // adjoint x=0 ∧ trace x=0} =
      1+(Nat.card F^12-1)*(Nat.card F^4+1) := by
  rw [card_white_cone_partition,card_whiteZero_first_diagonal,
    Nat.card_congr (whiteSecondDiagonalEquiv (F:=F)),card_white_chart_third_zero,
    ZeroDiagonal.card_locus]
  exact whiteZero_count_polynomial _ (by have := Finite.one_lt_card (α:=F); omega)

end Atlas.Albert

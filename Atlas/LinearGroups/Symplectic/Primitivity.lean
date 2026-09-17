import Atlas.LinearGroups.Symplectic.PointCount
import Atlas.Algebra.GeometricSumBounds
import Atlas.GroupTheory.RankThreePrimitivity

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F] [Finite F]

theorem card_suborbit_two_power (hn : 0 < n) (p : Points n F) :
    Nat.card {q : Points n F // suborbitIndex p q=2} = Nat.card F^(2*n-1) := by
  rw [card_suborbit_two,card_points_sum,card_perpendicular_points_sum]
  have hdim : 2*n=(2*n-1)+1 := by omega
  change Atlas.Arithmetic.geometricSum (Nat.card F) (2*n) -
    Atlas.Arithmetic.geometricSum (Nat.card F) (2*n-1) = _
  rw [hdim,Atlas.Arithmetic.geometricSum_succ]
  simp

/-- The actual projective action is primitive in rank at least two, including q=2 and q=3. -/
theorem projective_preprimitive (hn : 2 ≤ n) :
    MulAction.IsPreprimitive (PSp n F) (Points n F) := by
  classical
  let p : Points n F := ePoint ⟨0,by omega⟩
  let q := Nat.card F
  let A := pointSum q (2*n-1)
  let t := q^(2*n-1)
  let d : Fin 3 → ℕ := ![1,A-1,t]
  have hq : 2 ≤ q := Finite.one_lt_card
  have hm : 2 ≤ 2*n-1 := by omega
  have hdim : 2*n=(2*n-1)+1 := by omega
  have hA : 1 < A := Atlas.Arithmetic.geometricSum_gt_one hq hm
  have hN : Nat.card (Points n F) = A+t := by
    rw [card_points_sum]
    change Atlas.Arithmetic.geometricSum q (2*n) = _
    rw [hdim,Atlas.Arithmetic.geometricSum_succ]
    rfl
  have hnd := Atlas.Arithmetic.geometric_block_nondivisibility hq hm
  have hfirst : ¬ A ∣ Nat.card (Points n F) := by
    rw [card_points_sum,hdim]
    exact hnd.1
  have hsecond : ¬ (1+t) ∣ Nat.card (Points n F) := by
    rw [card_points_sum,hdim]
    exact hnd.2
  apply Atlas.GroupTheory.primitive_of_rankThree_nondivisibility p (suborbitIndex p)
    (suborbitIndex_self p) (fun x y h => suborbitIndex_transitive hn p x y h) d rfl
  · intro i
    fin_cases i
    · exact card_suborbit_zero p
    · change Nat.card {q : Points n F // suborbitIndex p q=1}=A-1
      rw [card_suborbit_one,card_perpendicular_points_sum]
    · exact card_suborbit_two_power (by omega) p
  · change Nat.card (Points n F)=1+(A-1)+t
    omega
  · change ¬ (1+(A-1)) ∣ Nat.card (Points n F)
    have he : 1+(A-1)=A := by omega
    rwa [he]
  · exact hsecond

end Atlas.Symplectic

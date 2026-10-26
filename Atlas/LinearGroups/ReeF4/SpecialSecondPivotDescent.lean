import Atlas.LinearGroups.ReeF4.SpecialSecondPivot
import Atlas.LinearGroups.ReeF4.SpecialSecondPivotVanishing

noncomputable section
set_option maxRecDepth 4096
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def secondPivotDescent {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (u : TraceZero F) : Model F m :=
  ⟨weylRho,weylOperator_mem_modelSubgroup m 0⟩ * secondPivot hcard u

/-- Actual descent from leading C4 (grade11) to leading C3 (grade8): all
four coordinates of higher absolute grade vanish and C3 retains the old C4. -/
theorem specialVector_C4_descent {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) {u : TraceZero F}
    (hu : IsSpecialVector m u) (hA4 : u.val.2 0 7 = 0)
    (hC4 : u.val.2 2 7 ≠ 0) :
    let z := (secondPivotDescent hcard u).val u
    IsSpecialVector m z ∧ z.val.2 0 7 = 0 ∧ z.val.2 2 7 = 0 ∧
      z.val.2 1 7 = 0 ∧ z.val.2 1 6 = 0 ∧
      z.val.2 2 6 = u.val.2 2 7 ∧ z.val.2 2 6 ≠ 0 := by
  let w := (secondPivot hcard u).val u
  have hw : IsSpecialVector m w := secondPivot_special hcard hu
  have ha : w.val.2 0 7 = 0 := (secondPivot_preserves_A4 hcard u).trans hA4
  have hb3 : w.val.2 1 6 = 0 := secondPivot_B3_zero hcard u hC4
  have hb4 : w.val.2 1 7 = 0 := secondPivot_B4_zero hcard u hC4
  have hc : w.val.2 2 7 ≠ 0 := by
    rw [show w.val.2 2 7 = u.val.2 2 7 from secondPivot_preserves_C4 hcard u]
    exact hC4
  have hf := hw.C3_zero_of_reduced_C4 hcard ha hb3 hb4 hc
  refine ⟨hu.map_model (secondPivotDescent hcard u),?_,?_,?_,?_,?_,?_⟩
  · exact ha
  · exact hf
  · exact hb3
  · exact hb4
  · exact secondPivot_preserves_C4 hcard u
  · exact hc
end Atlas.ReeF4

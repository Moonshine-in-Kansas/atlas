import Atlas.Algebra.FiniteHadamardTwo
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Tactic.Abel

/-! UNCOMPILED source candidate. The exponential commutator of a
length-three positive operator string, over a rational algebra only. -/

noncomputable section
namespace Atlas.Algebra

variable {S : Type*} [Ring S] [Algebra ℚ S]

/-- The double-edge exponential identity with all operator relations and
the exact nilpotence hypotheses visible. No target group is assumed. -/
theorem exp_doubleEdge_commutator
    (A B C D : S) (hA : IsNilpotent A) (hB : IsNilpotent B)
    (hC : IsNilpotent C) (hD : IsNilpotent ((1 / 2 : ℚ) • D))
    (hAB : A * B - B * A = C) (hAC : A * C - C * A = D)
    (hAD : Commute A D) (hBC : Commute B C)
    (hBD : Commute B D) (hCD : Commute C D) :
    IsNilpotent.exp A * IsNilpotent.exp B * IsNilpotent.exp (-A) *
      IsNilpotent.exp (-B) =
        IsNilpotent.exp C * IsNilpotent.exp ((1 / 2 : ℚ) • D) := by
  let u : Sˣ :=
    ⟨IsNilpotent.exp A, IsNilpotent.exp (-A),
      IsNilpotent.exp_mul_exp_neg_self hA, IsNilpotent.exp_neg_mul_exp_self hA⟩
  have hmap := IsNilpotent.exp_smul (ConjAct.toConjAct u) hB
  change IsNilpotent.exp (IsNilpotent.exp A * B * IsNilpotent.exp (-A)) =
    IsNilpotent.exp A * IsNilpotent.exp B * IsNilpotent.exp (-A) at hmap
  rw [exp_mul_mul_exp_neg_eq_add_add_half A B C D hA hAB hAC hAD] at hmap
  have hCDhalf : Commute C ((1 / 2 : ℚ) • D) := hCD.smul_right _
  have hBsum : Commute B (C + (1 / 2 : ℚ) • D) :=
    hBC.add_right (hBD.smul_right _)
  have hsumNil : IsNilpotent (C + (1 / 2 : ℚ) • D) :=
    hCDhalf.isNilpotent_add hC hD
  have horder : B + C + (1 / 2 : ℚ) • D = (C + (1 / 2 : ℚ) • D) + B := by abel
  rw [← hmap, horder,
    IsNilpotent.exp_add_of_commute hBsum.symm hsumNil hB, mul_assoc,
    IsNilpotent.exp_mul_exp_neg_self hB, mul_one,
    IsNilpotent.exp_add_of_commute hCDhalf hC hD]

end Atlas.Algebra

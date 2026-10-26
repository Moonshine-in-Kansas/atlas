import Atlas.Algebra.CentralBracketExponential
import Atlas.Algebra.FiniteHadamardTwo
import Mathlib.Algebra.Ring.Action.ConjAct

/-! Source candidate: a finite class-three commutator formula. The two
third-degree brackets are explicit and commute with the remaining factors.
There is no analytic exponential or BCH assumption. -/

noncomputable section
namespace Atlas.Algebra
variable {S : Type*} [Ring S] [Algebra ℚ S]

/-- A length-three string with a second, central bracket correction. -/
theorem exp_classThree_commutator (A B C D E : S)
    (hA : IsNilpotent A) (hB : IsNilpotent B) (hC : IsNilpotent C)
    (hD : IsNilpotent D) (hE : IsNilpotent E)
    (hAB : A*B-B*A=C) (hAC : A*C-C*A=D) (hBC : B*C-C*B=E)
    (hAD : Commute A D) (hBD : Commute B D) (hCD : Commute C D)
    (hBE : Commute B E) (hCE : Commute C E) (hDE : Commute D E) :
    IsNilpotent.exp A * IsNilpotent.exp B * IsNilpotent.exp (-A) * IsNilpotent.exp (-B) =
      IsNilpotent.exp C * IsNilpotent.exp ((1/2:ℚ) • D) *
        IsNilpotent.exp ((1/2:ℚ) • E) := by
  let Q := C + (1/2:ℚ) • D
  have hQ : IsNilpotent Q := (hCD.smul_right (1/2:ℚ)).isNilpotent_add hC (hD.smul _)
  have hQE : Commute Q E := hCE.add_left (hDE.smul_left _)
  have hBQ : B*Q-Q*B=E := by
    calc
      B*Q-Q*B = (B*C-C*B) + (1/2:ℚ) • (B*D-D*B) := by
        simp only [Q,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,smul_sub]
        module
      _ = E := by rw [hBC,sub_eq_zero.mpr hBD.eq,smul_zero,add_zero]
  let u : Sˣ := ⟨IsNilpotent.exp A, IsNilpotent.exp (-A),
    IsNilpotent.exp_mul_exp_neg_self hA, IsNilpotent.exp_neg_mul_exp_self hA⟩
  have hconj : IsNilpotent.exp A * B * IsNilpotent.exp (-A) = B+Q := by
    simpa only [Q,add_assoc] using exp_mul_mul_exp_neg_eq_add_add_half A B C D hA hAB hAC hAD
  have hsum : IsNilpotent (B+Q) := by
    have h := hB.map (MulSemiringAction.toRingHom (ConjAct Sˣ) S (ConjAct.toConjAct u))
    change IsNilpotent (IsNilpotent.exp A * B * IsNilpotent.exp (-A)) at h
    rwa [hconj] at h
  have hcancel : B+Q+ -B=Q := by abel
  have hbr : (B+Q)*(-B)-(-B)*(B+Q)=E := by
    calc
      (B+Q)*(-B)-(-B)*(B+Q)=B*Q-Q*B := by noncomm_ring
      _=E := hBQ
  have hsplit := exp_mul_eq_exp_add_mul_exp_half_bracket (B+Q) (-B) E
    hsum hB.neg hE (hcancel.symm ▸ hQ) hbr (hBE.add_left hQE) hBE.neg_left
  rw [hcancel] at hsplit
  have hmap := IsNilpotent.exp_smul (ConjAct.toConjAct u) hB
  change IsNilpotent.exp (IsNilpotent.exp A * B * IsNilpotent.exp (-A)) =
    IsNilpotent.exp A * IsNilpotent.exp B * IsNilpotent.exp (-A) at hmap
  rw [hconj] at hmap
  rw [← hmap,hsplit,IsNilpotent.exp_add_of_commute (hCD.smul_right _) hC (hD.smul _)]

end Atlas.Algebra

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.NoncommRing

/-! A four-factor polynomial identity for square-zero operators with vanishing
alternating triple products. No characteristic or nilpotence-of-bracket premise. -/

namespace Atlas.Algebra

theorem squareZero_commutator_expansion {S : Type*} [Ring S]
    (a b : S) (haa : a * a = 0) (hbb : b * b = 0)
    (haba : a * b * a = 0) (hbab : b * a * b = 0) :
    (1 + a) * (1 + b) * (1 - a) * (1 - b) = 1 + (a * b - b * a) := by
  have haba' : a * (b * a) = 0 := by simpa only [mul_assoc] using haba
  have hbab' : b * (a * b) = 0 := by simpa only [mul_assoc] using hbab
  have habab : a * (b * (a * b)) = 0 := by
    calc
      a * (b * (a * b)) = (a * b * a) * b := by simp only [mul_assoc]
      _ = 0 := by rw [haba, zero_mul]
  noncomm_ring [haa, hbb, haba', hbab', habab]

/-- Central scalar parameters enter only through their product. -/
theorem squareZero_scaled_commutator_expansion
    {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    (a b : S) (haa : a * a = 0) (hbb : b * b = 0)
    (haba : a * b * a = 0) (hbab : b * a * b = 0) (s t : R) :
    (1 + s • a) * (1 + t • b) * (1 + (-s) • a) * (1 + (-t) • b) =
      1 + (s * t) • (a * b - b * a) := by
  have hsa : (s • a) * (s • a) = 0 := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, haa, smul_zero]
  have htb : (t • b) * (t • b) = 0 := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hbb, smul_zero]
  have hsatbsa : (s • a) * (t • b) * (s • a) = 0 := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, haba, smul_zero]
  have htbsatb : (t • b) * (s • a) * (t • b) = 0 := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hbab, smul_zero]
  calc
    _ = 1 + ((s • a) * (t • b) - (t • b) * (s • a)) := by
      simpa only [neg_smul, sub_eq_add_neg] using
        squareZero_commutator_expansion (s • a) (t • b) hsa htb hsatbsa htbsatb
    _ = _ := by
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub, mul_comm t s]

end Atlas.Algebra

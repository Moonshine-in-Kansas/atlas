import Atlas.LinearGroups.Chevalley.Integral.StringExponential
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! # Explicit finite-string Weyl operators.

The signed anti-diagonal formula holds over every commutative ring. The bound n≤3
comes from the actual root-string theorem; finite checking here concerns at
most four basis vectors, never an enumeration of a Chevalley group. -/
noncomputable section
namespace Atlas.Chevalley.Integral
variable {R : Type*} [CommRing R]

 theorem unit_scalar_pow_cancel (t : Rˣ) (p q : ℕ) :
    t.val^p * t.inv^q = t.val^(p-q) * t.inv^(q-p) := by
  by_cases h : q ≤ p
  · have hp : (p-q)+q=p := Nat.sub_add_cancel h
    calc
      t.val^p * t.inv^q = (t.val^(p-q)*t.val^q)*t.inv^q := by rw [← pow_add, hp]
      _ = t.val^(p-q)*(t.val*t.inv)^q := by rw [mul_pow, mul_assoc]
      _ = _ := by simp [Nat.sub_eq_zero_of_le h]
  · have h' : p ≤ q := by omega
    have hq : p+(q-p)=q := Nat.add_sub_of_le h'
    calc
      t.val^p * t.inv^q = t.val^p*(t.inv^p*t.inv^(q-p)) := by rw [← pow_add, hq]
      _ = (t.val*t.inv)^p*t.inv^(q-p) := by rw [mul_pow, mul_assoc]
      _ = _ := by simp [Nat.sub_eq_zero_of_le h']

 theorem unit_scalar_mul_pow_cancel (t : Rˣ) (q : ℕ) :
    t.val * t.inv^q = t.val^(1-q)*t.inv^(q-1) := by
  simpa only [pow_one] using unit_scalar_pow_cancel t 1 q

 theorem unit_scalar_pow_mul_cancel (t : Rˣ) (p : ℕ) :
    t.val^p * t.inv = t.val^(p-1)*t.inv^(1-p) := by
  simpa only [pow_one] using unit_scalar_pow_cancel t p 1

theorem unit_coe_pow_cancel (t : Rˣ) (p q : ℕ) :
    (t : R)^p * ((t⁻¹ : Rˣ) : R)^q =
      (t : R)^(p-q) * ((t⁻¹ : Rˣ) : R)^(q-p) :=
  unit_scalar_pow_cancel t p q

/-- Reverse the actual finite binomial string to obtain the lowering exponential. -/
def stringLowerExponential (n : ℕ) (t : R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  (stringExponential n t).submatrix Fin.rev Fin.rev

/-- The rank-one Weyl word on the finite integral string representation. -/
def stringWeyl (n : ℕ) (t : Rˣ) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  stringExponential n t.val * stringLowerExponential n (-t.inv) * stringExponential n t.val

set_option maxHeartbeats 800000 in
 theorem stringWeyl_entry_0 (t : Rˣ) (i j : Fin (0+1)) :
    stringWeyl 0 t i j =
      if i = j.rev then (-1:R)^j.val * t.val^(0-j.val)*t.inv^j.val else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [stringWeyl, stringLowerExponential, Matrix.mul_apply, Fin.sum_univ_succ,
      stringExponential_entry, Fin.rev, Nat.choose]

set_option maxHeartbeats 800000 in
 theorem stringWeyl_entry_1 (t : Rˣ) (i j : Fin (1+1)) :
    stringWeyl 1 t i j =
      if i = j.rev then (-1:R)^j.val * t.val^(1-j.val)*t.inv^j.val else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [stringWeyl, stringLowerExponential, Matrix.mul_apply, Fin.sum_univ_succ,
      stringExponential_entry, Fin.rev, Nat.choose]

set_option maxHeartbeats 800000 in
 theorem stringWeyl_entry_2 (t : Rˣ) (i j : Fin (2+1)) :
    stringWeyl 2 t i j =
      if i = j.rev then (-1:R)^j.val * t.val^(2-j.val)*t.inv^j.val else 0 := by
  have h12 := unit_coe_pow_cancel t 1 2
  norm_num at h12
  have h21 := unit_coe_pow_cancel t 2 1
  norm_num at h21
  have h22 := unit_coe_pow_cancel t 2 2
  norm_num at h22
  have h31 := unit_coe_pow_cancel t 3 1
  norm_num at h31
  have h32 := unit_coe_pow_cancel t 3 2
  norm_num at h32
  have h42 := unit_coe_pow_cancel t 4 2
  norm_num at h42
  have r12 := (mul_comm (((t⁻¹ : Rˣ) : R)^2) ((t : R)^1)).trans (unit_coe_pow_cancel t 1 2)
  norm_num at r12
  have r22 := (mul_comm (((t⁻¹ : Rˣ) : R)^2) ((t : R)^2)).trans (unit_coe_pow_cancel t 2 2)
  norm_num at r22
  fin_cases i <;> fin_cases j <;>
    norm_num [stringWeyl, stringLowerExponential, Matrix.mul_apply, Fin.sum_univ_succ,
      stringExponential_entry, Fin.rev, Nat.choose] <;>
    ring_nf <;>
    (try simp only [r12, r22, h12, h21, h22, h31, h32, h42]) <;> norm_num <;> first | rfl | ring

set_option maxHeartbeats 800000 in
 theorem stringWeyl_entry_3 (t : Rˣ) (i j : Fin (3+1)) :
    stringWeyl 3 t i j =
      if i = j.rev then (-1:R)^j.val * t.val^(3-j.val)*t.inv^j.val else 0 := by
  have h12 := unit_coe_pow_cancel t 1 2
  norm_num at h12
  have h13 := unit_coe_pow_cancel t 1 3
  norm_num at h13
  have h21 := unit_coe_pow_cancel t 2 1
  norm_num at h21
  have h22 := unit_coe_pow_cancel t 2 2
  norm_num at h22
  have h23 := unit_coe_pow_cancel t 2 3
  norm_num at h23
  have h31 := unit_coe_pow_cancel t 3 1
  norm_num at h31
  have h32 := unit_coe_pow_cancel t 3 2
  norm_num at h32
  have h33 := unit_coe_pow_cancel t 3 3
  norm_num at h33
  have h41 := unit_coe_pow_cancel t 4 1
  norm_num at h41
  have h42 := unit_coe_pow_cancel t 4 2
  norm_num at h42
  have h43 := unit_coe_pow_cancel t 4 3
  norm_num at h43
  have h52 := unit_coe_pow_cancel t 5 2
  norm_num at h52
  have h53 := unit_coe_pow_cancel t 5 3
  norm_num at h53
  have h63 := unit_coe_pow_cancel t 6 3
  norm_num at h63
  have r12 := (mul_comm (((t⁻¹ : Rˣ) : R)^2) ((t : R)^1)).trans (unit_coe_pow_cancel t 1 2)
  norm_num at r12
  have r13 := (mul_comm (((t⁻¹ : Rˣ) : R)^3) ((t : R)^1)).trans (unit_coe_pow_cancel t 1 3)
  norm_num at r13
  have r22 := (mul_comm (((t⁻¹ : Rˣ) : R)^2) ((t : R)^2)).trans (unit_coe_pow_cancel t 2 2)
  norm_num at r22
  have r23 := (mul_comm (((t⁻¹ : Rˣ) : R)^3) ((t : R)^2)).trans (unit_coe_pow_cancel t 2 3)
  norm_num at r23
  have r33 := (mul_comm (((t⁻¹ : Rˣ) : R)^3) ((t : R)^3)).trans (unit_coe_pow_cancel t 3 3)
  norm_num at r33
  fin_cases i <;> fin_cases j <;>
    norm_num [stringWeyl, stringLowerExponential, Matrix.mul_apply, Fin.sum_univ_succ,
      stringExponential_entry, Fin.rev, Nat.choose] <;>
    ring_nf <;>
    (try simp only [r12, r13, r22, r23, r33, h12, h13, h21, h22, h23, h31, h32, h33, h41, h42, h43, h52, h53, h63]) <;> norm_num <;> first | rfl | ring

 theorem stringWeyl_entry (n : ℕ) (hn : n ≤ 3) (t : Rˣ) (i j : Fin (n+1)) :
    stringWeyl n t i j =
      if i = j.rev then (-1:R)^j.val * t.val^(n-j.val)*t.inv^j.val else 0 := by
  interval_cases n
  · exact stringWeyl_entry_0 t i j
  · exact stringWeyl_entry_1 t i j
  · exact stringWeyl_entry_2 t i j
  · exact stringWeyl_entry_3 t i j

end Atlas.Chevalley.Integral

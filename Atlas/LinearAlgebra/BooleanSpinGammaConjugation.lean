import Atlas.LinearAlgebra.BooleanSpinGamma

/-! Local conjugation of the actual Boolean gamma vector space. The formulas
are polynomial over every commutative ring and use no Clifford faithfulness. -/
noncomputable section
namespace Atlas.BooleanSpin
open Classical
open scoped BigOperators
variable {I : Type*} [Fintype I] [LinearOrder I]
variable (R : Type*) [CommRing R]

private theorem step_axis (i j : I) (b : Bool) (x y : R) :
    step R i b * axis R j x y + axis R j x y * step R i b =
      if i=j then (if b then y else x) • 1 else 0 := by
  by_cases hij : i=j
  · subst j
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      calc
        _ = x • (creation R i * annihilation R i + annihilation R i * creation R i) := by
          simp only [axis, creation, annihilation, mul_add, add_mul,
            mul_smul_comm, smul_mul_assoc, step_square, smul_zero, smul_add]
          module
        _ = _ := by rw [creation_annihilation]
    · simp only [↓reduceIte]
      calc
        _ = y • (creation R i * annihilation R i + annihilation R i * creation R i) := by
          simp only [axis, creation, annihilation, mul_add, add_mul,
            mul_smul_comm, smul_mul_assoc, step_square, smul_zero, smul_add]
          module
        _ = _ := by rw [creation_annihilation]
  · simp only [if_neg hij, axis, creation, annihilation, mul_add, add_mul,
      mul_smul_comm, smul_mul_assoc, step_anticomm R i j hij, smul_neg]
    module

private theorem step_parity (i : I) (b : Bool) :
    step R i b * parity R + parity R * step R i b = 0 := by
  rw [parity_step]
  exact add_neg_cancel (step R i b * parity R : Module.End R (Space (I := I) R))

theorem step_gamma (i : I) (b : Bool) (x y : I → R) (z : R) :
    step R i b * gamma R x y z + gamma R x y z * step R i b =
      (if b then y i else x i) • 1 := by
  calc
    _ = (∑ j, (step R i b * axis R j (x j) (y j) +
        axis R j (x j) (y j) * step R i b)) +
        z • (step R i b * parity R + parity R * step R i b) := by
      simp only [gamma, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
        mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_add]
      module
    _ = _ := by simp [step_axis, step_parity]

theorem parity_gamma (x y : I → R) (z : R) :
    parity R * gamma R x y z + gamma R x y z * parity R = (2*z) • 1 := by
  calc
    _ = (∑ j, (parity R * axis R j (x j) (y j) +
        axis R j (x j) (y j) * parity R)) +
        z • (parity R * parity R + parity R * parity R) := by
      simp only [gamma, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
        mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_add]
      module
    _ = _ := by simp only [parity_axis, Finset.sum_const_zero, zero_add,
        parity_square, smul_add]; module

/- The literal LinearMap operations are fixed in these statements before
applying the generic ring lemmas. No instance is added or replaced. -/
private theorem end_mul_sub (f g h : Module.End R (Space (I := I) R)) :
    f * (g-h) = f*g-f*h := by
  exact mul_sub f g h

private theorem end_sub_mul (f g h : Module.End R (Space (I := I) R)) :
    (f-g) * h = f*h-g*h := by
  exact sub_mul f g h

private theorem end_mul_neg (f g : Module.End R (Space (I := I) R)) :
    f * (-g) = -(f*g) := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro sigma
  simp only [Module.End.mul_apply, LinearMap.neg_apply,
    LinearMap.map_neg, Finsupp.neg_apply]

private theorem end_neg_mul (f g : Module.End R (Space (I := I) R)) :
    (-f) * g = -(f*g) := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro sigma
  simp only [Module.End.mul_apply, LinearMap.neg_apply, Finsupp.neg_apply]

private theorem end_neg_neg (f : Module.End R (Space (I := I) R)) :
    - -f = f := by
  exact neg_neg f

private theorem end_neg_zero : -(0 : Module.End R (Space (I := I) R)) = 0 := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro sigma
  simp only [LinearMap.neg_apply, LinearMap.zero_apply,
    Finsupp.neg_apply, Finsupp.zero_apply, neg_zero]

private theorem end_sub_self (f : Module.End R (Space (I := I) R)) : f-f=0 := by
  exact sub_self f

private theorem end_eq_sub_of_add_eq {f g h : Module.End R (Space (I := I) R)}
    (heq : f+h=g) : f=g-h := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro sigma
  have hcoeff := congrArg (fun A : Module.End R (Space (I := I) R) => A v sigma) heq
  simp only [LinearMap.add_apply, Finsupp.add_apply] at hcoeff
  simp only [LinearMap.sub_apply, Finsupp.sub_apply]
  linear_combination hcoeff

private theorem end_apply_sub (f : Module.End R (Space (I := I) R))
    (v w : Space (I := I) R) : f (v-w) = f v-f w := by
  exact f.map_sub v w

set_option backward.isDefEq.respectTransparency false in
private theorem conjugation_expansion (N G : Module.End R (Space (I := I) R)) (t : R) :
    (1+t • N)*G*(1-t • N) = G + t • (N*G-G*N) - t^2 • (N*G*N) := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro sigma
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, end_apply_sub (I := I) R,
    LinearMap.map_add, LinearMap.map_smul, Finsupp.add_apply,
    Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Every long-root operator is square-zero; no characteristic assumption. -/
theorem long_square (i j : I) (hij : i ≠ j) :
    (creation R i * annihilation R j) * (creation R i * annihilation R j) = 0 := by
  calc
    _ = creation R i * (annihilation R j * creation R i) * annihilation R j := by
      simp only [mul_assoc]
    _ = 0 := by
      rw [step_anticomm R j i (Ne.symm hij) false true]
      simp only [creation, annihilation, end_mul_neg (I := I) R, end_neg_mul (I := I) R, ← mul_assoc, step_square, zero_mul, end_neg_zero (I := I) R]

set_option backward.isDefEq.respectTransparency false in
/-- The long root changes x_i by t*x_j and y_j by -t*y_i. -/
theorem long_gamma (i j : I) (hij : i ≠ j) (t : R) (x y : I → R) (z : R) :
    (1+t • (creation R i*annihilation R j))*gamma R x y z*
      (1-t • (creation R i*annihilation R j)) =
      gamma R x y z + (t*x j) • creation R i - (t*y i) • annihilation R j := by
  let G : Module.End R (Space (I := I) R) := gamma R x y z
  let c : Module.End R (Space (I := I) R) := creation R i
  let a : Module.End R (Space (I := I) R) := annihilation R j
  have hc : c*G = y i • 1-G*c  := by
    apply end_eq_sub_of_add_eq (I := I) R
    exact step_gamma R i true x y z
  have ha : a*G = x j • 1-G*a  := by
    apply end_eq_sub_of_add_eq (I := I) R
    exact step_gamma R j false x y z
  have hac : a*c = -(c*a) := step_anticomm R j i (Ne.symm hij) false true
  have hcc : c*c=0 := step_square R i true
  have haa : a*a=0 := step_square R j false
  have hd : (c*a)*G-G*(c*a) = x j • c-y i • a := by
    rw [mul_assoc c a G, ha, end_mul_sub (I := I) R, ← mul_assoc c G a, hc]
    simp only [mul_smul_comm, mul_one, end_sub_mul (I := I) R, smul_mul_assoc, one_mul]
    apply LinearMap.ext
    intro v
    apply Finsupp.ext
    intro sigma
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.zero_apply,
      Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply,
      Finsupp.neg_apply, Finsupp.zero_apply, smul_eq_mul]
    ring
  have hNG : (c*a)*G = G*(c*a)+(x j • c-y i • a) := by rw [← hd]; abel
  have hn : (c*a)*G*(c*a) = 0 := by
    have hN : (c*a)*(c*a)=0 := long_square R i j hij
    have hcN : c*(c*a)=0 := by rw [← mul_assoc, hcc, zero_mul]
    have haN : a*(c*a)=0 := by
      rw [← mul_assoc, hac]
      simp only [end_neg_mul (I := I) R, mul_assoc, haa, mul_zero, end_neg_zero (I := I) R]
    calc
      _ = G*((c*a)*(c*a))+(x j • c-y i • a)*(c*a) := by rw [hNG]; noncomm_ring
      _ = 0 := by simp only [hN, mul_zero, zero_add, end_sub_mul (I := I) R,
          smul_mul_assoc, hcN, haN, smul_zero, end_sub_self (I := I) R]
  change (1+t • (c*a))*G*(1-t • (c*a)) = _
  rw [conjugation_expansion, hd, hn]
  dsimp only [G, c, a]
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro sigma
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.zero_apply,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply,
    Finsupp.neg_apply, Finsupp.zero_apply, smul_eq_mul]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The short raising operator is c_i P. -/
theorem short_upper_square (i : I) :
    (creation R i*parity R)*(creation R i*parity R) = 0 := by
  calc
    _ = creation R i*(parity R*creation R i)*parity R := by simp only [mul_assoc]
    _ = 0 := by
      rw [parity_step]
      simp only [creation, annihilation, end_mul_neg (I := I) R, end_neg_mul (I := I) R, ← mul_assoc, step_square, zero_mul, end_neg_zero (I := I) R]

set_option backward.isDefEq.respectTransparency false in
/-- The short lowering operator is P a_i. -/
theorem short_lower_square (i : I) :
    (parity R*annihilation R i)*(parity R*annihilation R i) = 0 := by
  calc
    _ = parity R*(annihilation R i*parity R)*annihilation R i := by simp only [mul_assoc]
    _ = 0 := by
      have hp : annihilation R i*parity R = -(parity R*annihilation R i) := by
        simpa only [annihilation, end_neg_neg (I := I) R] using
          congrArg (fun A : Module.End R (Space (I := I) R) => -A)
            (parity_step R i false).symm
      rw [hp]
      simp only [annihilation, end_mul_neg (I := I) R, end_neg_mul (I := I) R, mul_assoc, step_square, mul_zero, end_neg_zero (I := I) R]

set_option backward.isDefEq.respectTransparency false in
/-- Explicit upper short-root correction: x_i+=2tz-t²y_i and z-=ty_i. -/
theorem short_upper_gamma (i : I) (t : R) (x y : I → R) (z : R) :
    (1+t • (creation R i*parity R))*gamma R x y z*
      (1-t • (creation R i*parity R)) = gamma R x y z +
      (2*t*z-t^2*y i) • creation R i - (t*y i) • parity R := by
  let G : Module.End R (Space (I := I) R) := gamma R x y z
  let c : Module.End R (Space (I := I) R) := creation R i
  let P : Module.End R (Space (I := I) R) := parity (I := I) R
  have hc : c*G = y i • 1-G*c  := by
    apply end_eq_sub_of_add_eq (I := I) R
    exact step_gamma R i true x y z
  have hP : P*G = (2*z) • 1-G*P  := by
    apply end_eq_sub_of_add_eq (I := I) R
    exact parity_gamma R x y z
  have hPc : P*c = -(c*P) := parity_step R i true
  have hcc : c*c=0 := step_square R i true
  have hPP : P*P=1 := parity_square R
  have hd : (c*P)*G-G*(c*P) = (2*z) • c-y i • P := by
    rw [mul_assoc c P G, hP, end_mul_sub (I := I) R, ← mul_assoc c G P, hc]
    simp only [mul_smul_comm, mul_one, end_sub_mul (I := I) R, smul_mul_assoc, one_mul]
    apply LinearMap.ext
    intro v
    apply Finsupp.ext
    intro sigma
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.zero_apply,
      Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply,
      Finsupp.neg_apply, Finsupp.zero_apply, smul_eq_mul]
    ring
  have hNG : (c*P)*G = G*(c*P)+((2*z) • c-y i • P) := by rw [← hd]; abel
  have hn : (c*P)*G*(c*P) = y i • c := by
    have hN : (c*P)*(c*P)=0 := short_upper_square R i
    have hcN : c*(c*P)=0 := by rw [← mul_assoc, hcc, zero_mul]
    have hPN : P*(c*P) = -c := by
      rw [← mul_assoc, hPc]
      simp only [end_neg_mul (I := I) R, mul_assoc, hPP, mul_one]
    calc
      _ = G*((c*P)*(c*P))+((2*z) • c-y i • P)*(c*P) := by rw [hNG]; noncomm_ring
      _ = _ := by
        rw [hN, mul_zero, zero_add, end_sub_mul (I := I) R,
          smul_mul_assoc, smul_mul_assoc, hcN, hPN]
        apply LinearMap.ext
        intro v
        apply Finsupp.ext
        intro sigma
        simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.zero_apply,
          Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply,
          Finsupp.neg_apply, Finsupp.zero_apply, smul_eq_mul]
        ring
  change (1+t • (c*P))*G*(1-t • (c*P)) = _
  rw [conjugation_expansion, hd, hn]
  dsimp only [G, c, P]
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro sigma
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.zero_apply,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply,
    Finsupp.neg_apply, Finsupp.zero_apply, smul_eq_mul]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Explicit lower short-root correction: y_i-=2tz+t²x_i and z+=tx_i. -/
theorem short_lower_gamma (i : I) (t : R) (x y : I → R) (z : R) :
    (1+t • (parity R*annihilation R i))*gamma R x y z*
      (1-t • (parity R*annihilation R i)) = gamma R x y z -
      (2*t*z+t^2*x i) • annihilation R i + (t*x i) • parity R := by
  let G : Module.End R (Space (I := I) R) := gamma R x y z
  let a : Module.End R (Space (I := I) R) := annihilation R i
  let P : Module.End R (Space (I := I) R) := parity (I := I) R
  have ha : a*G = x i • 1-G*a  := by
    apply end_eq_sub_of_add_eq (I := I) R
    exact step_gamma R i false x y z
  have hP : P*G = (2*z) • 1-G*P  := by
    apply end_eq_sub_of_add_eq (I := I) R
    exact parity_gamma R x y z
  have haP : a*P = -(P*a) := by
    simpa only [a, P, annihilation, end_neg_neg (I := I) R] using
      congrArg (fun A : Module.End R (Space (I := I) R) => -A)
        (parity_step R i false).symm
  have haa : a*a=0 := step_square R i false
  have hPP : P*P=1 := parity_square R
  have hd : (P*a)*G-G*(P*a) = x i • P-(2*z) • a := by
    rw [mul_assoc P a G, ha, end_mul_sub (I := I) R, ← mul_assoc P G a, hP]
    simp only [mul_smul_comm, mul_one, end_sub_mul (I := I) R, smul_mul_assoc, one_mul]
    apply LinearMap.ext
    intro v
    apply Finsupp.ext
    intro sigma
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.zero_apply,
      Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply,
      Finsupp.neg_apply, Finsupp.zero_apply, smul_eq_mul]
    ring
  have hNG : (P*a)*G = G*(P*a)+(x i • P-(2*z) • a) := by rw [← hd]; abel
  have hn : (P*a)*G*(P*a) = x i • a := by
    have hN : (P*a)*(P*a)=0 := short_lower_square R i
    have hPN : P*(P*a)=a := by rw [← mul_assoc, hPP, one_mul]
    have haN : a*(P*a)=0 := by
      rw [← mul_assoc, haP]
      simp only [end_neg_mul (I := I) R, mul_assoc, haa, mul_zero, end_neg_zero (I := I) R]
    calc
      _ = G*((P*a)*(P*a))+(x i • P-(2*z) • a)*(P*a) := by rw [hNG]; noncomm_ring
      _ = _ := by
        rw [hN, mul_zero, zero_add, end_sub_mul (I := I) R,
          smul_mul_assoc, smul_mul_assoc, hPN, haN]
        apply LinearMap.ext
        intro v
        apply Finsupp.ext
        intro sigma
        simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.zero_apply,
          Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply,
          Finsupp.neg_apply, Finsupp.zero_apply, smul_eq_mul]
        ring
  change (1+t • (P*a))*G*(1-t • (P*a)) = _
  rw [conjugation_expansion, hd, hn]
  dsimp only [G, a, P]
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro sigma
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.zero_apply,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply,
    Finsupp.neg_apply, Finsupp.zero_apply, smul_eq_mul]
  ring

end Atlas.BooleanSpin

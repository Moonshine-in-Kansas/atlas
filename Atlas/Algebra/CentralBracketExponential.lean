import Atlas.Algebra.PolynomialFiniteExponential
import Atlas.Algebra.FiniteHadamard
import Mathlib.RingTheory.Polynomial.Nilpotent
import Mathlib.Tactic.NoncommRing

/-! Source candidate: central-bracket splitting by differentiation of a
finite polynomial identity. All nilpotence hypotheses are explicit. -/

noncomputable section
namespace Atlas.Algebra
open Polynomial

variable {S : Type*} [Ring S] [Algebra ℚ S]

/-- The bounded central-bracket exponential identity. In particular,
nilpotence of `P+Q` is a separate hypothesis, not inferred from the two
individual nilpotence hypotheses. -/
theorem exp_mul_eq_exp_add_mul_exp_half_bracket
    (P Q H : S) (hP : IsNilpotent P) (hQ : IsNilpotent Q)
    (hH : IsNilpotent H) (hPQ : IsNilpotent (P + Q))
    (hbracket : P * Q - Q * P = H)
    (hPH : Commute P H) (hQH : Commute Q H) :
    IsNilpotent.exp P * IsNilpotent.exp Q =
      IsNilpotent.exp (P + Q) * IsNilpotent.exp ((1 / 2 : ℚ) • H) := by
  let p : S[X] := C P * X
  let q : S[X] := C Q * X
  let z : S[X] := C (P + Q) * X
  let r : S[X] := (-1 / 2 : ℚ) • (C H * X ^ 2)
  let T : S[X] := C H * X
  let E := IsNilpotent.exp p
  let F := IsNilpotent.exp q
  let D := IsNilpotent.exp (-z)
  let K := IsNilpotent.exp r
  let J := E * F
  have linearNil (A : S) (hA : IsNilpotent A) :
      IsNilpotent (C A * X : S[X]) := by
    simpa only [pow_one] using
      Polynomial.isNilpotent_C_mul_pow_X_of_isNilpotent 1 hA
  have hp : IsNilpotent p := linearNil P hP
  have hq : IsNilpotent q := linearNil Q hQ
  have hz : IsNilpotent z := linearNil (P + Q) hPQ
  have hr : IsNilpotent r :=
    (Polynomial.isNilpotent_C_mul_pow_X_of_isNilpotent 2 hH).smul _
  have linearComm {A B : S} (hAB : Commute A B) :
      Commute (C A * X : S[X]) (C B * X) :=
    ((hAB.map C).mul_right (commute_X (C A)).symm).mul_left
      ((commute_X (C B)).mul_right (Commute.refl X))
  have linearDerivativeComm (A : S) :
      Commute (C A * X : S[X]) (C A) :=
    (Commute.refl (C A)).mul_left (commute_X (C A))
  have hp' : p.derivative = C P := by simp only [p, derivative_C_mul_X]
  have hq' : q.derivative = C Q := by simp only [q, derivative_C_mul_X]
  have hz' : z.derivative = C (P + Q) := by simp only [z, derivative_C_mul_X]
  have hr' : r.derivative = -T := by
    simp only [r, derivative_smul, derivative_C_mul_X_sq, mul_two, C_add, add_mul]
    dsimp only [T]
    module
  have hrT : Commute r (-T) := by
    have h : Commute (C H * X ^ 2 : S[X]) (C H * X) :=
      ((Commute.refl (C H)).mul_right (commute_X (C H)).symm).mul_left
        ((commute_X_pow (C H) 2).mul_right ((Commute.refl X).pow_left 2))
    exact (h.smul_left (-1 / 2 : ℚ)).neg_right
  have hE' : E.derivative = E * C P := by
    have h := polynomial_derivative_exp_of_commute hp
      (show Commute p p.derivative by rw [hp']; exact linearDerivativeComm P)
    simpa only [E, hp'] using h
  have hF' : F.derivative = F * C Q := by
    have h := polynomial_derivative_exp_of_commute hq
      (show Commute q q.derivative by rw [hq']; exact linearDerivativeComm Q)
    simpa only [F, hq'] using h
  have hD' : D.derivative = D * (-(C P + C Q)) := by
    have hcomm : Commute (-z) (-z).derivative := by
      rw [derivative_neg, hz']
      exact (linearDerivativeComm (P + Q)).neg_left.neg_right
    have h := polynomial_derivative_exp_of_commute hz.neg hcomm
    simpa only [D, derivative_neg, hz', C_add] using h
  have hK' : K.derivative = (-T) * K := by
    have hcomm : Commute r r.derivative := by rw [hr']; exact hrT
    have h := polynomial_derivative_exp_of_commute hr hcomm
    change K.derivative = K * r.derivative at h
    rw [hr'] at h
    exact h.trans (commute_finiteExp_right hrT.symm).symm.eq
  have hPE : Commute (C P) E :=
    commute_finiteExp_right (linearDerivativeComm P).symm
  have hQF : Commute (C Q) F :=
    commute_finiteExp_right (linearDerivativeComm Q).symm
  have hpolyBracket : p * C Q - C Q * p = T := by
    calc
      p * C Q - C Q * p = (C P * C Q - C Q * C P) * X := by
        dsimp only [p]
        rw [mul_assoc, (commute_X (C Q)).eq]
        noncomm_ring
      _ = C (P * Q - Q * P) * X := by rw [C_sub, C_mul, C_mul]
      _ = T := by rw [hbracket]
  have hhad : E * C Q = (C Q + T) * E := by
    have hcomm : Commute p (p * C Q - C Q * p) := by
      rw [hpolyBracket]
      exact linearComm hPH
    have h := exp_mul_eq_add_bracket_mul_exp p (C Q) hp hcomm
    simpa only [hpolyBracket, E] using h
  have hJ' : J.derivative = (C P + C Q + T) * J := by
    change (E * F).derivative = (C P + C Q + T) * (E * F)
    rw [derivative_mul, hE', hF']
    calc
      E * C P * F + E * (F * C Q) =
          C P * (E * F) + (C Q + T) * (E * F) := by
        rw [hPE.symm.eq, hQF.symm.eq, ← mul_assoc E (C Q) F, hhad]
        simp only [mul_assoc]
      _ = (C P + C Q + T) * (E * F) := by noncomm_ring
  have hTJ : Commute T J :=
    (commute_finiteExp_right (linearComm hPH.symm)).mul_right
      (commute_finiteExp_right (linearComm hQH.symm))
  have hpathDerivative : (D * J * K).derivative = 0 := by
    rw [derivative_mul, derivative_mul, hD', hJ', hK']
    calc
      (D * (-(C P + C Q)) * J + D * ((C P + C Q + T) * J)) * K +
          (D * J) * ((-T) * K) = D * (T * J - J * T) * K := by noncomm_ring
      _ = 0 := by rw [sub_eq_zero.mpr hTJ.eq]; simp
  have hpathZero : (D * J * K).coeff 0 = 1 := by
    change constantCoeff (D * J * K) = 1
    simp only [J, D, E, F, K, map_mul]
    rw [IsNilpotent.map_exp hz.neg constantCoeff,
      IsNilpotent.map_exp hp constantCoeff,
      IsNilpotent.map_exp hq constantCoeff,
      IsNilpotent.map_exp hr constantCoeff]
    simp [p, q, z, r, constantCoeff_apply, map_rat_smul]
  have hpath : D * J * K = 1 := by
    letI : IsAddTorsionFree S := IsAddTorsionFree.of_module_rat S
    have h := Polynomial.eq_C_of_derivative_eq_zero hpathDerivative
    simpa only [hpathZero, C_1] using h
  let ev : S[X] →+* S :=
    Polynomial.eval₂RingHom' (RingHom.id S) 1 (fun A => Commute.one_right A)
  have heC (A : S) : ev (C A) = A := by simp [ev, Polynomial.eval₂RingHom']
  have heX : ev X = 1 := by simp [ev, Polynomial.eval₂RingHom']
  have hvalue := congrArg ev hpath
  simp only [J, D, E, F, K, map_mul, map_one] at hvalue
  rw [IsNilpotent.map_exp hz.neg ev, IsNilpotent.map_exp hp ev,
    IsNilpotent.map_exp hq ev, IsNilpotent.map_exp hr ev] at hvalue
  have hprod : IsNilpotent.exp (-(P + Q)) * IsNilpotent.exp P *
      IsNilpotent.exp Q * IsNilpotent.exp (-((1 / 2 : ℚ) • H)) = 1 := by
    simpa only [p, q, z, r, map_neg, map_mul, heC, heX, map_pow,
      map_rat_smul, one_pow, mul_one, neg_div, neg_smul, mul_assoc] using hvalue
  have hleft := congrArg (fun W => IsNilpotent.exp (P + Q) * W) hprod
  simp only [← mul_assoc, IsNilpotent.exp_mul_exp_neg_self hPQ, one_mul, mul_one] at hleft
  have hright := congrArg (fun W => W * IsNilpotent.exp ((1 / 2 : ℚ) • H)) hleft
  simpa only [mul_assoc, IsNilpotent.exp_neg_mul_exp_self (hH.smul (1 / 2 : ℚ)),
    mul_one] using hright

end Atlas.Algebra

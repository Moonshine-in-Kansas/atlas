import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.ConwayWales
open Polynomial

private theorem polynomial_four : (4 : Polynomial (ZMod 4)) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg (Polynomial.C : ZMod 4 →+* Polynomial (ZMod 4))
      (show (4 : ZMod 4) = 0 by decide)

private theorem polynomial_eight : (8 : Polynomial (ZMod 4)) = 0 := by
  linear_combination 2 * polynomial_four

private theorem polynomial_neg_three : (-3 : Polynomial (ZMod 4)) = 1 := by
  linear_combination -polynomial_four

/-- The three actual factors of the seven-block cyclic polynomial over Z/4. -/
def cyclicFactorZero : Polynomial (ZMod 4) := X - 1
def cyclicFactorPlus : Polynomial (ZMod 4) := X^3 + 2*X^2 + X - 1
def cyclicFactorMinus : Polynomial (ZMod 4) := X^3 - X^2 + 2*X - 1

theorem cyclic_factorization :
    (X^7 - 1 : Polynomial (ZMod 4)) =
      cyclicFactorZero * cyclicFactorPlus * cyclicFactorMinus := by
  unfold cyclicFactorZero cyclicFactorPlus cyclicFactorMinus
  ring_nf
  simp only [polynomial_four, mul_zero, add_zero, sub_zero]

theorem cyclic_factors_zero_plus : IsCoprime cyclicFactorZero cyclicFactorPlus := by
  refine ⟨X^2 + 3*X, 3, ?_⟩
  unfold cyclicFactorZero cyclicFactorPlus
  ring_nf
  simp only [polynomial_four, polynomial_eight, polynomial_neg_three, mul_zero, add_zero]

theorem cyclic_factors_zero_minus : IsCoprime cyclicFactorZero cyclicFactorMinus := by
  refine ⟨-(X^2 + 2), 1, ?_⟩
  unfold cyclicFactorZero cyclicFactorMinus
  ring

theorem cyclic_factors_plus_minus : IsCoprime cyclicFactorPlus cyclicFactorMinus := by
  refine ⟨2 + 3*X, 1 + X, ?_⟩
  unfold cyclicFactorPlus cyclicFactorMinus
  ring_nf
  simp only [polynomial_four, polynomial_eight, polynomial_neg_three, mul_zero, add_zero]

/-- The cyclic coefficient ring for seven blocks. -/
abbrev CyclicRing := Polynomial (ZMod 4) ⧸ Ideal.span {(X^7 - 1 : Polynomial (ZMod 4))}
abbrev CyclicComponent (f : Polynomial (ZMod 4)) := Polynomial (ZMod 4) ⧸ Ideal.span {f}

private noncomputable def coprimeQuotient (f g : Polynomial (ZMod 4)) (h : IsCoprime f g) :
    CyclicComponent (f*g) ≃+* CyclicComponent f × CyclicComponent g :=
  (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton f g).symm).trans
    (Ideal.quotientMulEquivQuotientProd _ _ ((Ideal.isCoprime_span_singleton_iff f g).mpr h))

/-- Actual CRT isomorphism; no component sizes or code ranks are assumptions. -/
noncomputable def cyclicCRT : CyclicRing ≃+*
    CyclicComponent cyclicFactorZero ×
      (CyclicComponent cyclicFactorPlus × CyclicComponent cyclicFactorMinus) :=
  (Ideal.quotEquivOfEq (congrArg (fun f : Polynomial (ZMod 4) => Ideal.span {f})
    (cyclic_factorization.trans (mul_assoc _ _ _)))).trans
    ((coprimeQuotient _ _ (cyclic_factors_zero_plus.mul_right cyclic_factors_zero_minus)).trans
      (RingEquiv.prodCongr (RingEquiv.refl _) (coprimeQuotient _ _ cyclic_factors_plus_minus)))

end Atlas.ConwayWales


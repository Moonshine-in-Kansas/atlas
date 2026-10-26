import Atlas.Algebra.TwoStepExponential
import Atlas.Algebra.PolynomialFiniteExponential
import Atlas.LinearGroups.Chevalley.Integral.GeckExponentialRational
import Atlas.LinearGroups.Chevalley.Adjoint
import Mathlib.GroupTheory.Commutator.Basic

/-! Source-only rational transfer from actual conjugated raising operators
into the actual adjoint group. No root-coherence or projection hypothesis. -/

noncomputable section
namespace Atlas.Chevalley
open Integral
open scoped commutatorElement

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R] [Algebra ℚ R]

/-- A literal conjugate of a root element is the finite exponential of the
corresponding conjugated raising matrix. -/
theorem adjoint_conjugateX_val_eq_exp (u : Adjoint P b R) (i : b.support) (s : R) :
    (u * adjointX P b R i s * u⁻¹).val.val =
      IsNilpotent.exp (s • (u.val.val * raisingOver P b R i * (u⁻¹).val.val)) := by
  have h := IsNilpotent.exp_smul (ConjAct.toConjAct u.val)
    ((raisingOver_nilpotent P b R i).smul s)
  change IsNilpotent.exp (u.val.val * (s • raisingOver P b R i) * (u⁻¹).val.val) =
    u.val.val * IsNilpotent.exp (s • raisingOver P b R i) * (u⁻¹).val.val at h
  rw [mul_smul_comm, smul_mul_assoc,
    ← raisingExponential_eq_nilpotent_exp P b R i s] at h
  exact h.symm

/-- Inversion of the literal conjugate corresponds to negating its parameter. -/
theorem adjoint_conjugateX_inv_val_eq_exp (u : Adjoint P b R) (i : b.support) (s : R) :
    ((u * adjointX P b R i s * u⁻¹)⁻¹).val.val =
      IsNilpotent.exp (-(s • (u.val.val * raisingOver P b R i * (u⁻¹).val.val))) := by
  rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc]
  change (u * adjointX P b R i (-s) * u⁻¹).val.val = _
  rw [adjoint_conjugateX_val_eq_exp, neg_smul]

private theorem conjugateRaising_nilpotent (u : Adjoint P b R) (i : b.support) :
    IsNilpotent (u.val.val * raisingOver P b R i * (u⁻¹).val.val) :=
  (raisingOver_nilpotent P b R i).map
    (MulSemiringAction.toRingHom
      (ConjAct (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)ˣ)
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) (ConjAct.toConjAct u.val))

/-- Commuting actual conjugated operators give commuting actual root elements. -/
theorem adjoint_conjugateX_commute_of_operator_commute
    (u v : Adjoint P b R) (i j : b.support)
    (h : Commute (u.val.val * raisingOver P b R i * (u⁻¹).val.val)
      (v.val.val * raisingOver P b R j * (v⁻¹).val.val)) (s t : R) :
    Commute (u * adjointX P b R i s * u⁻¹) (v * adjointX P b R j t * v⁻¹) := by
  apply show (∀ g h : Adjoint P b R, g.val.val = h.val.val → g = h) from
    fun _ _ he => Subtype.ext (Units.ext he)
  change (u * adjointX P b R i s * u⁻¹).val.val *
      (v * adjointX P b R j t * v⁻¹).val.val =
    (v * adjointX P b R j t * v⁻¹).val.val *
      (u * adjointX P b R i s * u⁻¹).val.val
  simp only [adjoint_conjugateX_val_eq_exp]
  have hs := (h.smul_left s).smul_right t
  exact (Atlas.Algebra.commute_finiteExp_right
    (Atlas.Algebra.commute_finiteExp_right hs).symm).symm.eq

/-- A central two-step bracket gives the literal actual root commutator.
All three involved operators are conjugates of actual simple raising matrices. -/
theorem adjoint_conjugateX_commutator_of_operator_twoStep
    (u v w : Adjoint P b R) (i j k : b.support) (c : R)
    (hbr :
      (u.val.val * raisingOver P b R i * (u⁻¹).val.val) *
          (v.val.val * raisingOver P b R j * (v⁻¹).val.val) -
        (v.val.val * raisingOver P b R j * (v⁻¹).val.val) *
          (u.val.val * raisingOver P b R i * (u⁻¹).val.val) =
        c • (w.val.val * raisingOver P b R k * (w⁻¹).val.val))
    (hleft : Commute (u.val.val * raisingOver P b R i * (u⁻¹).val.val)
      (w.val.val * raisingOver P b R k * (w⁻¹).val.val))
    (hright : Commute (v.val.val * raisingOver P b R j * (v⁻¹).val.val)
      (w.val.val * raisingOver P b R k * (w⁻¹).val.val)) (s t : R) :
    ⁅u * adjointX P b R i s * u⁻¹, v * adjointX P b R j t * v⁻¹⁆ =
      w * adjointX P b R k (c*s*t) * w⁻¹ := by
  let E := u.val.val * raisingOver P b R i * (u⁻¹).val.val
  let F := v.val.val * raisingOver P b R j * (v⁻¹).val.val
  let H := w.val.val * raisingOver P b R k * (w⁻¹).val.val
  change E*F-F*E = c • H at hbr
  have hsbr : (s • E) * (t • F) - (t • F) * (s • E) = (c*s*t) • H := by
    calc
      (s • E) * (t • F) - (t • F) * (s • E) = (s*t) • (E*F-F*E) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm t s, smul_sub]
      _ = (c*s*t) • H := by
        rw [hbr, smul_smul]
        congr 1
        ring
  have hnil : IsNilpotent ((s • E) * (t • F) - (t • F) * (s • E)) := by
    rw [hsbr]
    exact (conjugateRaising_nilpotent P b R w k).smul (c*s*t)
  have hL : Commute (s • E) ((s • E) * (t • F) - (t • F) * (s • E)) := by
    rw [hsbr]
    exact (hleft.smul_left s).smul_right (c*s*t)
  have hR : Commute (t • F) ((s • E) * (t • F) - (t • F) * (s • E)) := by
    rw [hsbr]
    exact (hright.smul_left t).smul_right (c*s*t)
  have he := Atlas.Algebra.exp_commutator_eq_exp_bracket (s • E) (t • F)
    ((conjugateRaising_nilpotent P b R u i).smul s)
    ((conjugateRaising_nilpotent P b R v j).smul t) hnil hL hR
  rw [hsbr] at he
  apply Subtype.ext
  apply Units.ext
  change (u * adjointX P b R i s * u⁻¹).val.val *
      (v * adjointX P b R j t * v⁻¹).val.val *
      ((u * adjointX P b R i s * u⁻¹)⁻¹).val.val *
      ((v * adjointX P b R j t * v⁻¹)⁻¹).val.val =
    (w * adjointX P b R k (c*s*t) * w⁻¹).val.val
  simpa only [adjoint_conjugateX_val_eq_exp, adjoint_conjugateX_inv_val_eq_exp, E, F, H] using he

end Atlas.Chevalley

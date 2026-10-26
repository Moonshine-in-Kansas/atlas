import Atlas.GroupTheory.RootCommutatorPolarization
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylSameRoot
import Atlas.LinearGroups.Chevalley.WeightCompanionDoubleEdgeCommutator
import Atlas.LinearGroups.Chevalley.WeightCompanionB2MarkedLongRoot

/-! The actual short--short commutator at every double edge, including
characteristic two. The coefficient 2 is obtained by additive polarization
of the already proved mixed word, without division in the coefficient ring. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
open scoped commutatorElement

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

include hdiamond

set_option maxHeartbeats 800000 in
/-- With i short and j long, the short positive families of labels i and
s_j(i) have commutator in the highest long family s_i(j), with parameter -2st.
The equality holds in the actual full companion over every commutative ring. -/
theorem weightCompanionX_b2_short_short_commutator
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2)
    (s t : R) :
    ⁅weightCompanionX P b O hc hm R i s,
      weightCompanionWeyl P b O hc hm R j 1 *
        weightCompanionX P b O hc hm R i t *
          (weightCompanionWeyl P b O hc hm R j 1)⁻¹⁆ =
      weightCompanionWeyl P b O hc hm R i 1 *
        weightCompanionX P b O hc hm R j (-2 * s * t) *
          (weightCompanionWeyl P b O hc hm R i 1)⁻¹ := by
  let ni := weightCompanionWeyl P b O hc hm R i 1
  let nj := weightCompanionWeyl P b O hc hm R j 1
  let x := weightCompanionXHom P b O hc hm R i
  let z := (MulAut.conj nj).toMonoidHom.comp x
  let w := (MulAut.conj ni).toMonoidHom.comp (weightCompanionXHom P b O hc hm R j)
  have hxval (a : R) : x (Multiplicative.ofAdd a) =
      weightCompanionX P b O hc hm R i a := rfl
  have hzval (a : R) : z (Multiplicative.ofAdd a) =
      nj * weightCompanionX P b O hc hm R i a * nj⁻¹ := by
    simp only [z, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hxval]
  have hwval (a : R) : w (Multiplicative.ofAdd a) =
      ni * weightCompanionX P b O hc hm R j a * ni⁻¹ := by
    simp only [w, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, weightCompanionXHom, MonoidHom.coe_mk,
      OneHom.coe_mk, toAdd_ofAdd]
  have hcomm (a : R) :
      ⁅x (Multiplicative.ofAdd a), weightCompanionX P b O hc hm R j 1⁆ =
        z (Multiplicative.ofAdd (-a)) * w (Multiplicative.ofAdd (a ^ 2)) := by
    rw [hxval, hzval, hwval]
    simpa only [mul_one (-a), mul_one (a ^ 2)] using
      weightCompanionX_b2_commutator_eq_weyl_product P b hdiamond O hc hm R
        i j hne hij hji a 1
  have hxw (a c : R) : Commute (x (Multiplicative.ofAdd a))
      (w (Multiplicative.ofAdd c)) := by
    rw [hxval, hwval]
    exact weightCompanionX_commute_sameWeyl_conjugate_X P b O hc hm R hdiamond
      i j hne a c
  have hzw (a c : R) : Commute (z (Multiplicative.ofAdd a))
      (w (Multiplicative.ofAdd c)) := by
    have h0 := hxw a c
    rw [hxval, hwval] at h0
    have h := h0.map (MulAut.conj nj).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    have hfixed : nj * (ni * weightCompanionX P b O hc hm R j c * ni⁻¹) * nj⁻¹ =
        ni * weightCompanionX P b O hc hm R j c * ni⁻¹ :=
      weightCompanionWeyl_b2_fixes_long_conjugate_X P b hdiamond O hc hm R
        i j hne hij hji c
    rw [hfixed] at h
    rw [hzval, hwval]
    exact h
  have h := Atlas.GroupTheory.root_commutator_polarization x z w
    (weightCompanionX P b O hc hm R j 1) hcomm hxw hzw s t
  simpa only [hxval, hzval, hwval] using h

end Atlas.Chevalley

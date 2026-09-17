import Atlas.LinearAlgebra.QuadraticSquareSpinorInvolution
import Atlas.LinearGroups.Orthogonal.BAllRanksStructure
import Mathlib.GroupTheory.OrderOfElement

/-! # Actual representatives of every possible odd-B involution minus dimension -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F : Type*} [Field F] [Finite F]

theorem exists_B_involution_of_half_minus_dim (n m : ℕ) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (h2 : (2 : F) ≠ 0) :
    ∃ a : elementarySubgroup (formB n F), orderOf a = 2 ∧
      Module.finrank F (Atlas.LinearInvolution.minus a.val.val.toLinearMap) = 2*m := by
  letI : Invertible (2 : F) := invertibleOfNonzero h2
  obtain ⟨g,hg,hdim,hdet,hspin⟩ := exists_square_spinor_involution h2
    (formB n F) (polarB_nondegenerate h2) n m vectorB_finrank hmn
  let t : O_B n F := (isometryCarrierEquiv (formB n F)).symm g
  have ht : t ∈ elementarySubgroup (formB n F) := by
    rw [B_odd_intrinsic_all_rank n hn h2]
    constructor
    · change t.val.det = 1
      apply Units.ext
      change (g.toLinearEquiv.det : F) = 1
      rw [LinearEquiv.coe_det]
      exact hdet
    · change wallDeterminantClass (formB n F) (polarB_nondegenerate h2)
        (isometryCarrierEquiv (formB n F) t) = 1
      exact hspin
  let a : elementarySubgroup (formB n F) := ⟨t,ht⟩
  have hp : a^2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact hg x
  have hne : a ≠ 1 := by
    intro he
    have hz : Atlas.LinearInvolution.minus g.toLinearEquiv.toLinearMap = ⊥ := by
      apply bot_unique
      intro x hx
      have hneg : g x = -x := (Atlas.LinearInvolution.mem_minus _ _).mp hx
      have hfix : g x = x := congrArg (fun b : elementarySubgroup (formB n F) => b.val.val x) he
      have hx0 : (2 : F) • x = 0 := by
        calc
          _ = x + x := two_smul F x
          _ = g x + x := congrArg (fun y => y + x) hfix.symm
          _ = -x + x := congrArg (fun y => y + x) hneg
          _ = 0 := neg_add_cancel x
      exact (smul_eq_zero.mp hx0).resolve_left h2
    rw [hz,finrank_bot] at hdim
    omega
  exact ⟨a,orderOf_eq_prime_iff.mpr ⟨hp,hne⟩,hdim⟩
end Atlas.Orthogonal

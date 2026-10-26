import Atlas.LinearGroups.Chevalley.AdjointPerfectness
import Mathlib.Algebra.Ring.Int.Parity

/-! Odd Cartan ROW entries suffice for
perfectness in characteristic different from two. Our convention is
T_j(a) X_i(t) T_j(a)⁻¹ = X_i(a^(Cartan i j) t): i is the row. -/
noncomputable section
namespace Atlas.Chevalley
open Group
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (K : Type*) [Field K]

theorem adjointX_mem_commutator_of_odd_cartan
    (hchar : (-1 : K) ≠ 1) (i j : b.support)
    (hodd : Odd (b.cartanMatrix i j)) (t : K) :
    adjointX P b K i t ∈ commutator (Adjoint P b K) := by
  let a : Kˣ := Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)
  apply Atlas.GroupTheory.scaled_root_mem_commutator (adjointXHom P b K i)
    (adjointTorus P b K j a) (-1) hchar
  intro u
  simpa only [adjointXHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    a, Units.val_zpow_eq_zpow_val, Units.val_mk0, hodd.neg_one_zpow]
    using adjointTorus_conjugate_X P b K j i a u

theorem adjointY_mem_commutator_of_odd_cartan
    (hchar : (-1 : K) ≠ 1) (i j : b.support)
    (hodd : Odd (b.cartanMatrix i j)) (t : K) :
    adjointY P b K i t ∈ commutator (Adjoint P b K) := by
  let a : Kˣ := Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)
  apply Atlas.GroupTheory.scaled_root_mem_commutator (adjointYHom P b K i)
    (adjointTorus P b K j a) (-1) hchar
  intro u
  simpa only [adjointYHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    a, Units.val_zpow_eq_zpow_val, Units.val_mk0, hodd.neg.neg_one_zpow]
    using adjointTorus_conjugate_Y P b K j i a u

/-- Actual adjoint group; the hypothesis concerns its literal Cartan entries. -/
theorem adjoint_isPerfect_of_odd_cartan_rows (hchar : (-1 : K) ≠ 1)
    (hrows : ∀ i : b.support, ∃ j : b.support, Odd (b.cartanMatrix i j)) :
    IsPerfect (Adjoint P b K) := by
  apply isPerfect_def.mpr
  apply top_unique
  intro g hg
  apply adjoint_induction P b K ?_ ?_ (commutator _).one_mem
    (fun _ _ => (commutator _).mul_mem) (fun _ => (commutator _).inv_mem) g
  · intro i t
    obtain ⟨j,hj⟩ := hrows i
    exact adjointX_mem_commutator_of_odd_cartan P b K hchar i j hj t
  · intro i t
    obtain ⟨j,hj⟩ := hrows i
    exact adjointY_mem_commutator_of_odd_cartan P b K hchar i j hj t

end Atlas.Chevalley

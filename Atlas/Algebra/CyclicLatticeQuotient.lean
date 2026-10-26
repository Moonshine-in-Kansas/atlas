import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-! A cyclic lattice quotient from an explicit separating character.
The hypotheses are lattice data, independent of any group construction. -/
noncomputable section
namespace Atlas.Algebra
variable {M : Type*} [AddCommGroup M] (Q : Submodule ℤ M) (w : M)
  (n : ℕ) (χ : M →ₗ[ℤ] ZMod n)

theorem latticeCharacter_surjective (hw : χ w = 1) : Function.Surjective χ := by
  intro z
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨a • w, ?_⟩
  simp [map_smul, hw, zsmul_eq_mul]

theorem latticeCharacter_ker_eq
    (hQ : Q ≤ LinearMap.ker χ)
    (hspan : Q ⊔ Submodule.span ℤ {w} = ⊤)
    (hw : χ w = 1) (hnw : (n : ℤ) • w ∈ Q) :
    LinearMap.ker χ = Q := by
  apply le_antisymm ?_ hQ
  intro x hx
  have hmem : x ∈ Q ⊔ Submodule.span ℤ {w} := by rw [hspan]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hy0 : χ y = 0 := hQ hy
  have ha : (a : ZMod n) = 0 := by
    simpa only [LinearMap.mem_ker, map_add, map_smul, hy0, hw,
      zero_add, zsmul_eq_mul, mul_one] using hx
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a n).mp ha
  apply Q.add_mem hy
  rw [hk, mul_comm, ← smul_smul]
  exact Q.smul_mem k hnw

def cyclicLatticeQuotientEquiv
    (hQ : Q ≤ LinearMap.ker χ)
    (hspan : Q ⊔ Submodule.span ℤ {w} = ⊤)
    (hw : χ w = 1) (hnw : (n : ℤ) • w ∈ Q) :
    (M ⧸ Q) ≃ₗ[ℤ] ZMod n :=
  LinearEquiv.ofBijective (Q.liftQ χ hQ) ⟨
    LinearMap.ker_eq_bot.mp (Q.ker_liftQ_eq_bot χ hQ
      (latticeCharacter_ker_eq Q w n χ hQ hspan hw hnw).le),
    LinearMap.range_eq_top.mp (by
      rw [Q.range_liftQ χ hQ]
      exact LinearMap.range_eq_top.mpr (latticeCharacter_surjective w n χ hw))⟩

@[simp] theorem cyclicLatticeQuotientEquiv_mk
    (hQ : Q ≤ LinearMap.ker χ)
    (hspan : Q ⊔ Submodule.span ℤ {w} = ⊤)
    (hw : χ w = 1) (hnw : (n : ℤ) • w ∈ Q) (x : M) :
    cyclicLatticeQuotientEquiv Q w n χ hQ hspan hw hnw
      (Submodule.Quotient.mk x) = χ x := rfl

theorem cyclicLatticeQuotient_card [NeZero n]
    (hQ : Q ≤ LinearMap.ker χ)
    (hspan : Q ⊔ Submodule.span ℤ {w} = ⊤)
    (hw : χ w = 1) (hnw : (n : ℤ) • w ∈ Q) :
    Nat.card (M ⧸ Q) = n := by
  rw [Nat.card_congr (cyclicLatticeQuotientEquiv Q w n χ hQ hspan hw hnw).toEquiv]
  simp

end Atlas.Algebra

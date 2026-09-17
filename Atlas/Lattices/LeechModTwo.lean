import Atlas.Lattices.LeechSmallShells
import Mathlib.Algebra.Module.ZMod

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

def doubleLeech : leech →+ leech where
  toFun x := (2 : ℕ) • x
  map_zero' := by simp
  map_add' x y := nsmul_add x y 2

def twiceLeech : AddSubgroup leech := doubleLeech.range

/-- The quotient by twice the lattice, not ambient coordinate reduction. -/
abbrev LeechModTwo := leech ⧸ twiceLeech

def leechReduction : leech →+ LeechModTwo := QuotientAddGroup.mk' twiceLeech

theorem twiceLeech_mem (x : leech) : x ∈ twiceLeech ↔ ∃ y : leech, (2 : ℕ) • y = x := Iff.rfl

instance : Module Bit LeechModTwo := QuotientAddGroup.zmodModule (n := 2)
  (fun x => ⟨x,rfl⟩ : ∀ x : leech, (2 : ℕ) • x ∈ twiceLeech)

def leechBasisModTwo : leech →+ BinaryWord :=
  (coordinateMod 2).comp leechBasis.equivFun.toAddEquiv.toAddMonoidHom

theorem leechBasisModTwo_surjective : Function.Surjective leechBasisModTwo :=
  (coordinateMod_surjective 2).comp leechBasis.equivFun.surjective

theorem twiceLeech_eq_ker : twiceLeech = leechBasisModTwo.ker := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    change coordinateMod 2 (leechBasis.equivFun ((2 : ℕ) • y)) = 0
    rw [map_nsmul,map_nsmul]
    ext i
    simp [two_nsmul]
  · intro hx
    have hc : leechBasis.equivFun x ∈ (coordinateMod 2).ker := hx
    rw [← coordinateScale_range 2] at hc
    obtain ⟨y,hy⟩ := hc
    refine ⟨leechBasis.equivFun.symm y,?_⟩
    apply leechBasis.equivFun.injective
    change leechBasis.equivFun ((2 : ℕ) • leechBasis.equivFun.symm y) = _
    rw [map_nsmul,leechBasis.equivFun.apply_symm_apply]
    simpa only [coordinateScale,AddMonoidHom.coe_mk,ZeroHom.coe_mk,natCast_zsmul] using hy

def leechModTwoEquiv : LeechModTwo ≃+ BinaryWord :=
  (QuotientAddGroup.quotientAddEquivOfEq twiceLeech_eq_ker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective leechBasisModTwo leechBasisModTwo_surjective)

def leechModTwoLinearEquiv : LeechModTwo ≃ₗ[Bit] BinaryWord :=
  { leechModTwoEquiv with map_smul' := ZMod.map_smul leechModTwoEquiv }

instance : Finite LeechModTwo := Finite.of_equiv BinaryWord leechModTwoEquiv.symm

theorem leechModTwo_card : Nat.card LeechModTwo = 2 ^ 24 := by
  rw [Nat.card_congr leechModTwoEquiv.toEquiv]
  simp [Nat.card_pi,Nat.card_zmod,Omega,HexIndex]

theorem leechModTwo_finrank : Module.finrank Bit LeechModTwo = 24 := by
  rw [leechModTwoLinearEquiv.finrank_eq]
  simp [BinaryWord,Module.finrank_pi,Omega,HexIndex]

theorem leechReduction_surjective : Function.Surjective leechReduction :=
  QuotientAddGroup.mk'_surjective twiceLeech

theorem leechReduction_eq_zero (x : leech) : leechReduction x = 0 ↔ ∃ y : leech, (2 : ℕ) • y = x := by
  change (QuotientAddGroup.mk x : LeechModTwo) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  rfl

end Atlas.Lattices

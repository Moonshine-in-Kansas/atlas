import Atlas.Codes.GolayDuality
import Atlas.Codes.GolayDistribution
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual cocode of the retained marked Golay code. -/
abbrev Cocode := BinaryWord ⧸ golay

def cocodeFunctional : BinaryWord →ₗ[Bit] Module.Dual Bit golay :=
  golay.subtype.dualMap.comp binaryDot

theorem cocodeFunctional_apply (w : BinaryWord) (c : golay) :
    cocodeFunctional w c = binaryDot w c.val := rfl

theorem cocodeFunctional_ker : LinearMap.ker cocodeFunctional = golay := by
  ext w
  change (cocodeFunctional w = 0) ↔ w ∈ golay
  conv_rhs => rw [golay_selfDual]
  constructor
  · intro h c hc
    have he := LinearMap.congr_fun h (⟨c,hc⟩ : golay)
    change binaryDot w c = 0 at he
    rw [binaryDot_symmetric]
    exact he
  · intro h
    ext c
    change binaryDot w c.val = 0
    rw [binaryDot_symmetric]
    exact h c.val c.prop

theorem binaryDot_surjective : Function.Surjective (binaryDot (ι := Omega)) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank Bit BinaryWord = Module.finrank Bit (Module.Dual Bit BinaryWord)
      from (Subspace.dual_finrank_eq (K := Bit) (V := BinaryWord)).symm)).mp
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  exact binaryDot_nondegenerate.1 w (fun v => by
    have h := LinearMap.congr_fun hw v
    exact h)

theorem cocodeFunctional_surjective : Function.Surjective cocodeFunctional :=
  (LinearMap.dualMap_surjective_of_injective golay.injective_subtype).comp binaryDot_surjective

/-- Perfect pairing with the actual Golay code, realized as a linear equivalence. -/
def cocodeDualEquiv : Cocode ≃ₗ[Bit] Module.Dual Bit golay :=
  (Submodule.quotEquivOfEq golay (LinearMap.ker cocodeFunctional)
    cocodeFunctional_ker.symm).trans
    (cocodeFunctional.quotKerEquivOfSurjective cocodeFunctional_surjective)

theorem cocodeDualEquiv_mk (w : BinaryWord) (c : golay) :
    cocodeDualEquiv (Submodule.Quotient.mk w) c = binaryDot c.val w := by
  change binaryDot w c.val = binaryDot c.val w
  exact binaryDot_symmetric _ _

def cocodePairing (c : golay) (d : Cocode) : Bit := cocodeDualEquiv d c

def golayOne : golay := ⟨allOnes,C0_le_golay allOnes_mem_C0⟩

def cocodeParity : Cocode →ₗ[Bit] Bit :=
  (LinearMap.applyₗ' Bit golayOne).comp cocodeDualEquiv.toLinearMap

theorem cocodeParity_mk (w : BinaryWord) :
    cocodeParity (Submodule.Quotient.mk w) = binaryDot allOnes w :=
  cocodeDualEquiv_mk w golayOne

theorem cocode_finrank : Module.finrank Bit Cocode = 12 := by
  rw [cocodeDualEquiv.finrank_eq,Subspace.dual_finrank_eq,golay_finrank]

theorem cocode_card : Nat.card Cocode = 4096 := by
  letI : Fintype Cocode := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K := Bit),cocode_finrank]
  norm_num [Bit]

end Atlas.Fischer

import Atlas.LinearGroups.Chevalley.G2BinaryOrbit
import Atlas.LinearGroups.Chevalley.ModelG2Order
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.Subgroup.Simple

/-! Failure of simplicity for the actual uniform-engine G2 model at q=2.
The sign character acts on63 literal adjoint vectors, not an external model. -/
noncomputable section
namespace Atlas.Chevalley.G2Binary
open Classical G2Data

theorem actual_card : Nat.card G = 12096 := by
  change Nat.card (Model .G2 K) = 12096
  rw [model_G2_card]
  norm_num [Nat.card_zmod]

theorem model_binary_not_simple : ¬ IsSimpleGroup (Model .G2 K) := by
  intro hs
  letI : IsSimpleGroup G := hs
  rcases (inferInstance : oddSign.ker.Normal).eq_bot_or_eq_top with hk | hk
  · have hi := (MonoidHom.ker_eq_bot_iff oddSign).mp hk
    have hcard := Nat.card_le_card_of_injective oddSign hi
    rw [actual_card] at hcard
    norm_num [Nat.card_eq_fintype_card] at hcard
  · have hm : adjointX pairing base K (baseIndexEquiv 1) 1 ∈ oddSign.ker :=
      hk ▸ Subgroup.mem_top _
    have he : oddSign (adjointX pairing base K (baseIndexEquiv 1) 1) = 1 := hm
    rw [oddSign_short] at he
    exact (by decide : (-1 : ℤˣ) ≠ 1) he

end Atlas.Chevalley.G2Binary

namespace Atlas.Chevalley

theorem model_G2_two_not_simple (F : Type*) [Field F] [Finite F]
    (hq : Nat.card F = 2) : ¬ IsSimpleGroup (Model .G2 F) := by
  letI : Fintype F := Fintype.ofFinite F
  let e : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hq)
  intro hs
  letI := hs
  let f : Model RootType.G2 (ZMod 2) ≃* Model RootType.G2 F :=
    modelEquiv RootType.G2 e
  have hsource : IsSimpleGroup (Model RootType.G2 (ZMod 2)) :=
    MulEquiv.isSimpleGroup (G := Model RootType.G2 (ZMod 2))
      (H := Model RootType.G2 F) f
  exact G2Binary.model_binary_not_simple hsource

end Atlas.Chevalley

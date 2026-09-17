import Atlas.LinearGroups.G2.BinarySign
import Atlas.LinearGroups.G2.Simplicity
import Atlas.LinearGroups.G2.LocalFieldTransport

namespace Atlas.G2
variable {F : Type*} [Field F] [Finite F]

noncomputable def binaryFieldEquiv (hF : Nat.card F=2) : F ≃+* ZMod 2 := by
  letI := Fintype.ofFinite F
  exact (ZMod.ringEquivOfPrime F Nat.prime_two (by simpa [Nat.card_eq_fintype_card] using hF)).symm

 theorem card_longRootNormalClosure_binary (hF : Nat.card F=2) :
    Nat.card (longRootNormalClosure (F := F))=6048 := by
  rw [Nat.card_congr (longRootNormalClosureFieldEquiv (binaryFieldEquiv hF)).toEquiv]
  exact BinaryException.card_H

 theorem index_longRootNormalClosure_binary (hF : Nat.card F=2) :
    (longRootNormalClosure (F := F)).index=2 := by
  have hc := (longRootNormalClosure (F := F)).card_mul_index
  rw [card_longRootNormalClosure_binary hF,card_Model,hF] at hc
  norm_num at hc
  omega

 theorem not_simple_binary (hF : Nat.card F=2) : ¬ IsSimpleGroup (Model F) := by
  intro hs
  exact BinaryException.not_simple ((fieldEquiv (binaryFieldEquiv hF)).isSimpleGroup_congr.mp hs)

 theorem longRootNormalClosure_binary_nontrivial (hF : Nat.card F=2) :
    longRootNormalClosure (F := F) ≠ ⊥ := by
  intro h
  have hc := card_longRootNormalClosure_binary hF
  rw [h,Subgroup.card_bot] at hc
  contradiction

 theorem longRootNormalClosure_binary_proper (hF : Nat.card F=2) :
    longRootNormalClosure (F := F) ≠ ⊤ := by
  intro h
  have hi := index_longRootNormalClosure_binary hF
  rw [h,Subgroup.index_top] at hi
  contradiction

/-- Exact simplicity range of the full concrete octonion automorphism group. -/
theorem isSimple_iff : IsSimpleGroup (Model F) ↔ 2 < Nat.card F := by
  constructor
  · intro hs
    have hq : 1 < Nat.card F := Finite.one_lt_card (α := F)
    by_contra hn
    have he : Nat.card F=2 := by omega
    exact not_simple_binary he hs
  · exact isSimple

end Atlas.G2


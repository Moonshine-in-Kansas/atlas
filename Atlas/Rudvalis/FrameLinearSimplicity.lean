import Atlas.Rudvalis.FramePerfectLinearAlgebra
import Atlas.LinearGroups.PSLSimplicity
import Atlas.LinearGroups.ProjectiveSpecialLinear

/-! The actual Fano linear group is identified with the verified type-A group
PSL(3,2), using the trivial binary scalar center. -/
namespace Atlas.Rudvalis

theorem binarySL_center_eq_bot :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) Bit)=⊥ := by
  have hc : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) Bit))=1 := by
    rw [Atlas.card_sl_center]
    norm_num [Nat.card_eq_fintype_card,Bit,ZMod.card]
  have hs := (Nat.card_eq_one_iff_unique.mp hc).1
  apply (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) Bit)).eq_bot_iff_forall.mpr
  intro g hg
  exact congrArg Subtype.val (hs.elim ⟨g,hg⟩ 1)

theorem binarySLToLinear_injective : Function.Injective binarySLToLinear := by
  intro g h he
  have hh := binaryLinearMatrixEquiv.injective he
  apply Subtype.ext
  exact congrArg Units.val hh

noncomputable def binarySLLinearEquiv :
    Matrix.SpecialLinearGroup (Fin 3) Bit ≃* (E ≃ₗ[Bit] E) :=
  MulEquiv.ofBijective binarySLToLinear ⟨binarySLToLinear_injective,binarySLToLinear_surjective⟩

noncomputable def binaryPSLLinearEquiv :
    Matrix.ProjectiveSpecialLinearGroup (Fin 3) Bit ≃* (E ≃ₗ[Bit] E) :=
  ((QuotientGroup.quotientMulEquivOfEq binarySL_center_eq_bot).trans
    QuotientGroup.quotientBot).trans binarySLLinearEquiv

theorem binaryLinearGroup_simple : IsSimpleGroup (E ≃ₗ[Bit] E) := by
  let := Atlas.psl_simple_high_rank (F := Bit) 3 (by decide)
  exact binaryPSLLinearEquiv.symm.isSimpleGroup

/-- Both properties apply to the actual linear automorphisms used by the block homomorphism. -/
theorem binaryLinearGroup_simple_order :
    IsSimpleGroup (E ≃ₗ[Bit] E) ∧ Nat.card (E ≃ₗ[Bit] E)=168 :=
  ⟨binaryLinearGroup_simple,binaryLinearGroup_order⟩

end Atlas.Rudvalis

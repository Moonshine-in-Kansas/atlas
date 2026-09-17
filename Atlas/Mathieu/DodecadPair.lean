import Atlas.Mathieu.DodecadComplement
import Atlas.GroupTheory.PairStabilizer

noncomputable section
namespace Atlas.Codes
open scoped Pointwise

abbrev Mathieu12PairModel (D : Dodecad) :=
  Atlas.GroupTheory.PairStabilizer (G := Mathieu24CodeModel) D (dodecadComplement D)

def mathieu12PairRestriction (D : Dodecad) : Mathieu12PairModel D →*
    Equiv.Perm ({D,dodecadComplement D} : Set Dodecad) :=
  Atlas.GroupTheory.pairRestrictionHom D (dodecadComplement D)

theorem dodecad_pair_fixing (D : Dodecad) :
    fixingSubgroup Mathieu24CodeModel ({D,dodecadComplement D} : Set Dodecad) =
      Mathieu12DodecadModel D := by
  ext g
  constructor
  · intro hg; exact hg ⟨D,Or.inl rfl⟩
  · intro hg x
    change g • x.val = x.val
    rcases x.prop with hx | hx
    · rw [hx]; exact hg
    · rw [hx,dodecadComplement_equivariant]
      exact congrArg dodecadComplement hg

def mathieu12PairKernelEquiv (D : Dodecad) : (mathieu12PairRestriction D).ker ≃* Mathieu12DodecadModel D :=
  (Atlas.GroupTheory.pairRestrictionKernelEquiv D (dodecadComplement D)
    (dodecadComplement_ne D).symm).trans (MulEquiv.subgroupCongr (dodecad_pair_fixing D))

theorem mathieu12Pair_swap (D : Dodecad) :
    ∃ g : Mathieu12PairModel D, g.val • D = dodecadComplement D := by
  obtain ⟨g,hg⟩ := dodecad_transitive_explicit D (dodecadComplement D)
  have he : g • D = dodecadComplement D := Subtype.ext hg
  have hc : g • dodecadComplement D = D := by
    rw [dodecadComplement_equivariant,he]
    exact Subtype.ext (compl_compl D.val)
  exact ⟨⟨g,(Atlas.GroupTheory.pairStabilizer_mem D (dodecadComplement D)
    (dodecadComplement_ne D).symm g).mpr (Or.inr ⟨he,hc⟩)⟩,he⟩

theorem mathieu12PairRestriction_surjective (D : Dodecad) :
    Function.Surjective (mathieu12PairRestriction D) := by
  classical
  let f := mathieu12PairRestriction D
  obtain ⟨g,hg⟩ := mathieu12Pair_swap D
  have hn : f g ≠ 1 := by
    intro he
    have hx := congrArg (fun σ : Equiv.Perm ({D,dodecadComplement D} : Set Dodecad) =>
      (σ ⟨D,Or.inl rfl⟩).val) he
    change g.val • D = D at hx
    exact dodecadComplement_ne D (hg.symm.trans hx)
  haveI : Nontrivial f.range := ⟨⟨⟨f g,⟨g,rfl⟩⟩,1,fun he => hn (congrArg Subtype.val he)⟩⟩
  have hc : Nat.card (Equiv.Perm ({D,dodecadComplement D} : Set Dodecad)) = 2 := by
    rw [Nat.card_perm]
    simp [Nat.card_eq_fintype_card,(dodecadComplement_ne D).symm]
  have hl : 1 < Nat.card f.range := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  apply MonoidHom.range_eq_top.mp
  apply f.range.eq_top_of_card_eq
  have hu := Nat.card_le_card_of_injective f.range.subtype Subtype.val_injective
  omega

theorem mathieu12Pair_order (D : Dodecad) : Nat.card (Mathieu12PairModel D) = 190080 := by
  let f := mathieu12PairRestriction D
  have he := f.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr (mathieu12PairRestriction_surjective D),
    Subgroup.card_top,Nat.card_perm] at he
  rw [Nat.card_congr (mathieu12PairKernelEquiv D).toEquiv,mathieu12_order] at he
  classical
  norm_num [Nat.card_eq_fintype_card,(dodecadComplement_ne D).symm] at he
  rw [Nat.card_eq_fintype_card]
  exact he.symm

def mathieu12_to_pair (D : Dodecad) : Mathieu12DodecadModel D →* Mathieu12PairModel D :=
  (mathieu12PairRestriction D).ker.subtype.comp (mathieu12PairKernelEquiv D).symm.toMonoidHom

theorem mathieu12_to_pair_injective (D : Dodecad) : Function.Injective (mathieu12_to_pair D) :=
  Subtype.val_injective.comp (mathieu12PairKernelEquiv D).symm.injective

theorem mathieu12_to_pair_embedding (D : Dodecad) (g : Mathieu12DodecadModel D) :
    (mathieu12_to_pair D g).val = g.val := by
  have he := congrArg (fun g : Mathieu12DodecadModel D => g.val)
    ((mathieu12PairKernelEquiv D).apply_symm_apply g)
  exact he

theorem mathieu12_to_pair_range (D : Dodecad) :
    (mathieu12_to_pair D).range = (mathieu12PairRestriction D).ker := by
  ext g
  constructor
  · rintro ⟨h,rfl⟩
    exact ((mathieu12PairKernelEquiv D).symm h).prop
  · intro hg
    refine ⟨mathieu12PairKernelEquiv D ⟨g,hg⟩,?_⟩
    exact congrArg Subtype.val ((mathieu12PairKernelEquiv D).symm_apply_apply ⟨g,hg⟩)

theorem mathieu12_pair_index (D : Dodecad) : (mathieu12_to_pair D).range.index = 2 := by
  rw [mathieu12_to_pair_range,Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (mathieu12PairRestriction_surjective D),Subgroup.card_top,Nat.card_perm]
  classical
  simp [Nat.card_eq_fintype_card,(dodecadComplement_ne D).symm]

end Atlas.Codes

import Atlas.Rudvalis.CodeGroup
import Mathlib.GroupTheory.Index
import Atlas.Rudvalis.BinaryGroupOrder

/-! The exact kernel of the full signed code group's coordinate projection. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

private theorem kernel_right (g : codePermutationHom.ker) : g.val.val.right=1 :=
  (codePermutationHom_kernel g.val).mp g.prop

private theorem kernel_sign_mem (g : codePermutationHom.ker) :
    g.val.val.left.toAdd∈signPatterns := by
  apply (codeGroup_sign_mem _).mp
  have he : (SemidirectProduct.inl g.val.val.left : SignedCoordinates Coordinate)=g.val.val := by
    apply SemidirectProduct.ext
    · rfl
    · exact (kernel_right g).symm
  change SemidirectProduct.inl g.val.val.left∈codeGroup
  rw [he]
  exact g.val.prop

noncomputable def codeSignKernelEquiv :
    codePermutationHom.ker ≃* Multiplicative signPatterns where
  toFun g := Multiplicative.ofAdd ⟨g.val.val.left.toAdd,kernel_sign_mem g⟩
  invFun s := ⟨⟨SemidirectProduct.inl (Multiplicative.ofAdd s.toAdd.val),
    (codeGroup_sign_mem _).mpr s.toAdd.prop⟩,by
      apply (codePermutationHom_kernel _).mpr
      rfl⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact (kernel_right g).symm
  right_inv s := rfl
  map_mul' g h := by
    change (⟨(g.val.val*h.val.val).left.toAdd,_⟩ : signPatterns)=
      ⟨g.val.val.left.toAdd,_⟩+⟨h.val.val.left.toAdd,_⟩
    apply Subtype.ext
    change g.val.val.left.toAdd+(h.val.val.left.toAdd ∘ g.val.val.right.symm)=_
    rw [kernel_right g]
    rfl

theorem codePermutationHom_kernel_order : Nat.card codePermutationHom.ker=16 := by
  rw [Nat.card_congr codeSignKernelEquiv.toEquiv]
  change Nat.card signPatterns=16
  exact signPatterns_card

/-- The remaining order obligation is exactly surjectivity of this concrete map. -/
theorem codeGroup_order_of_surjective (h : Function.Surjective codePermutationHom) :
    Nat.card codeGroup=16*Nat.card binaryPermutationGroup := by
  rw [← codePermutationHom.ker.card_mul_index,Subgroup.index_ker,
    codePermutationHom_kernel_order]
  congr 1
  exact Nat.card_congr (Equiv.ofBijective (fun g : codePermutationHom.range => g.val)
    ⟨Subtype.val_injective,by intro g; exact ⟨⟨g,h g⟩,rfl⟩⟩)

theorem codeGroup_card_image :
    Nat.card codeGroup=16*Nat.card codePermutationHom.range := by
  rw [← codePermutationHom.ker.card_mul_index,Subgroup.index_ker,
    codePermutationHom_kernel_order]

theorem codeGroup_order_dvd : Nat.card codeGroup ∣ 1376256 := by
  have h := Nat.mul_dvd_mul_left 16 codePermutationHom.range.card_subgroup_dvd_card
  rw [← codeGroup_card_image,binaryPermutationGroup_order] at h
  exact h

end Atlas.Rudvalis

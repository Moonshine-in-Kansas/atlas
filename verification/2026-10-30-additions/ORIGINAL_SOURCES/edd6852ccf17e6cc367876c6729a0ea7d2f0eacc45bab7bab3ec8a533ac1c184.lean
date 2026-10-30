import Atlas.Comparisons.Exceptional.G2Binary.Derived
import Atlas.GroupTheory.KernelComplement
import Mathlib.GroupTheory.SemidirectProduct

namespace Atlas.G2.BinaryException
open Atlas.G2.Explicit

/-- The actual short-root involution supplies a complement to the derived group. -/
def shortRootComplement : Subgroup (Model K) where
  carrier := {g | g = 1 ∨ g = rootF 1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp [← pow_two, F_sq]
  inv_mem' := by
    rintro a (rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_left (by simpa [pow_two] using F_sq))

theorem shortRootComplement_sign_bijective :
    Function.Bijective (Binary.lineSign.comp shortRootComplement.subtype) := by
  constructor
  · intro x y he
    apply Subtype.ext
    rcases x.property with hx | hx <;> rcases y.property with hy | hy
    · exact hx.trans hy.symm
    · exfalso
      change Binary.lineSign x.val = Binary.lineSign y.val at he
      rw [hx,hy,map_one,Binary.lineSign_rootF_one] at he
      exact (by decide : (1 : ℤˣ) ≠ -1) he
    · exfalso
      change Binary.lineSign x.val = Binary.lineSign y.val at he
      rw [hx,hy,map_one,Binary.lineSign_rootF_one] at he
      exact (by decide : (-1 : ℤˣ) ≠ 1) he
    · exact hx.trans hy.symm
  · intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨⟨1,Or.inl rfl⟩,map_one _⟩
    · exact ⟨⟨rootF 1,Or.inr rfl⟩,Binary.lineSign_rootF_one⟩

noncomputable def shortRootComplementEquivSigns : shortRootComplement ≃* ℤˣ :=
  MulEquiv.ofBijective (Binary.lineSign.comp shortRootComplement.subtype)
    shortRootComplement_sign_bijective

theorem H_complement : H.IsComplement' shortRootComplement := by
  rw [← lineSign_kernel]
  exact Atlas.GroupTheory.isComplement_kernel_of_restriction_bijective
    Binary.lineSign shortRootComplement shortRootComplement_sign_bijective

/-- Internal splitting with its actual conjugation action. Identification of this
 action with the field involution on PSU3(3) is a separate, still open bridge. -/
noncomputable def binarySplitExtension :
    H ⋊[(H.normalizerMonoidHom).comp
      (Subgroup.inclusion (H.normalizer_eq_top ▸ le_top))] shortRootComplement ≃* Model K :=
  SemidirectProduct.mulEquivSubgroup H_complement

end Atlas.G2.BinaryException

import Mathlib.GroupTheory.Complement

namespace Atlas.GroupTheory

/-- A subgroup on which a quotient homomorphism is bijective is an actual
complement to its kernel. No finiteness or order assumptions are required. -/
theorem isComplement_kernel_of_restriction_bijective {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (K : Subgroup G) (hf : Function.Bijective (f.comp K.subtype)) :
    f.ker.IsComplement' K := by
  apply (Subgroup.isComplement_iff_bijective _ _).mpr
  constructor
  · rintro ⟨a,k⟩ ⟨b,l⟩ h
    have hk : k=l := hf.injective (by
      change f k.val=f l.val
      have he := congrArg f h
      simpa only [map_mul,show f a.val=1 from a.property,
        show f b.val=1 from b.property,one_mul] using he)
    subst l
    have hab : a=b := Subtype.ext (mul_right_cancel h)
    subst b
    rfl
  · intro g
    obtain ⟨k,hk⟩ := hf.surjective (f g)
    have hg : g*k.val⁻¹ ∈ f.ker := by
      change f (g*k.val⁻¹)=1
      rw [map_mul,map_inv,show f k.val=f g from hk,mul_inv_cancel]
    exact ⟨⟨⟨g*k.val⁻¹,hg⟩,k⟩,inv_mul_cancel_right g k.val⟩

end Atlas.GroupTheory

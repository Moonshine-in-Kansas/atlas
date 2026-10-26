import Atlas.Rudvalis.FrameSignDifferences
import Atlas.Rudvalis.HeavyBlockTransport
import Atlas.Rudvalis.ScalarQuotient

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

noncomputable def rowSignHom : Multiplicative (Point→Bit) →* SignedCoordinates Coordinate where
  toFun a := SemidirectProduct.inl (Multiplicative.ofAdd (rowSigns a.toAdd))
  map_one' := rfl
  map_mul' _ _ := rfl

theorem rowSignHom_mem_code (a : Point→Bit) (ha : a∈hammingSignCode) :
    rowSignHom (Multiplicative.ofAdd a)∈codeGroup :=
  (codeGroup_sign_mem _).mpr ((rowSigns_mem_iff a).mpr ha)

noncomputable def rowSignCode (a : hammingSignCode) : codeGroup :=
  ⟨rowSignHom (Multiplicative.ofAdd a.val),rowSignHom_mem_code a.val a.prop⟩

theorem signedCoordinates_sign_conjugate {ι : Type*} (g : SignedCoordinates ι) (s : ι→Bit) :
    g*SemidirectProduct.inl (Multiplicative.ofAdd s)*g⁻¹=
      SemidirectProduct.inl (Multiplicative.ofAdd (s∘g.right.symm)) := by
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left,SemidirectProduct.mul_right,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.inv_left,mul_one,
      ←MulAut.mul_apply,map_inv,mul_inv_cancel,MulAut.one_apply]
    change g.left*(signPermutationAction g.right (Multiplicative.ofAdd s))*g.left⁻¹=_
    rw [mul_comm g.left, mul_assoc,mul_inv_cancel,mul_one]
    rfl
  · simp

theorem rowSignHom_conjugate (g : codeGroup) (a : Point→Bit) :
    g.val*rowSignHom (Multiplicative.ofAdd a)*g.val⁻¹=
      rowSignHom (Multiplicative.ofAdd (a∘codeRowImage g⁻¹)) := by
  change g.val*SemidirectProduct.inl (Multiplicative.ofAdd (rowSigns a))*g.val⁻¹=
    SemidirectProduct.inl (Multiplicative.ofAdd (rowSigns (a∘codeRowImage g⁻¹)))
  rw [signedCoordinates_sign_conjugate]
  congr 1
  change (rowSigns a∘g.val.right.symm)=rowSigns (a∘codeRowImage g⁻¹)
  funext z
  change a (g.val.right.symm z).1=a (codeRowImage g⁻¹ z.1)
  exact congrArg a (codeRowImage_coordinates g⁻¹ z)

theorem codeRowImage_eq_linearPoint (g : codeGroup) :
    codeRowImage g=linearPointEquiv (codeBlockLinearHom g) := by
  funext p
  apply Subtype.ext
  have h := codeBlockLinear_coordinates g (p,0)
  rw [codeRowImage_coordinates] at h
  exact h.symm

end Atlas.Rudvalis

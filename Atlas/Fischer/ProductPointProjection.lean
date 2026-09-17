import Atlas.Fischer.AxisProductCoefficients

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- With disjoint octad-coordinate supports, only the point-point block can
contribute to any point coordinate of the actual algebra product. -/
theorem product_axis_apply_of_octad_disjoint (x y : Coordinates)
    (h : ∀ D : Octad, x (.inr D)=0 ∨ y (.inr D)=0) (i : Omega) :
    product x y (.inl i)=∑ a : Omega, ∑ b : Omega,
      (star (x (.inl a))*star (y (.inl b)))*axisBasisProduct a b (.inl i) := by
  classical
  have hw (D E : Octad) : (star (x (.inr D))*star (y (.inr E)))*
      octadBasisProduct D E (.inl i)=0 := by
    rw [octadBasisProduct_axis_apply]
    by_cases he : D=E
    · subst E
      rcases h D with hz | hz <;> simp [hz]
    · simp [he]
  unfold product
  simp only [Finset.sum_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Fintype.sum_sum_type,basisProduct,
    axisOctadBasisProduct_axis_apply,mul_zero,Finset.sum_const_zero,add_zero,zero_add,hw]

end Atlas.Fischer

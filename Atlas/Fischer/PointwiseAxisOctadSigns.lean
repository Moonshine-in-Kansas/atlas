import Atlas.Fischer.PointwiseAxisOctadLines

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Odd cocode commutation makes the diagonal scalar real. -/
theorem pointwiseAxis_octad_scalar_real (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (O : Octad) :
    star (e.val (xOctad O) (.inr O))=e.val (xOctad O) (.inr O) := by
  classical
  have hc : 0 < O.valᶜ.card := by
    rw [Finset.card_compl,octad_size O.val O.property]
    have h : Fintype.card Omega=24 := by decide
    rw [h]; decide
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hc
  have hi0 : i ∉ O.val := Finset.mem_compl.mp hi
  have h := semilinearAlgebra_rootMap e (basicAxis i) (xOctad O)
  rw [pointwiseAxis_fixes_basic e he i,pointwiseAxis_octad_line e he O,
    rootMap_smul,rootMap_basicAxis_xOctad,if_neg hi0] at h
  rw [pointwiseAxis_octad_line e he O] at h
  have hh := congrFun h (.inr O)
  simpa only [Pi.smul_apply,smul_eq_mul,xOctad_octad_apply,ite_true,mul_one] using hh

/-- The real diagonal scalars have square one by the retained intrinsic norm. -/
theorem pointwiseAxis_octad_scalar_square (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (O : Octad) :
    e.val (xOctad O) (.inr O)^2=1 := by
  have h := semilinearAlgebraAutomorphism_hermitian e (xOctad O) (xOctad O)
  rw [pointwiseAxis_octad_line e he O,hermitian_smul_left,hermitian_smul_right,
    hermitian_xOctad,if_pos rfl,map_one,pointwiseAxis_octad_scalar_real e he O,mul_one] at h
  simpa only [pow_two] using h

/-- Every pointwise axis stabilizer acts by an actual sign on each actual octad
basis vector. This is derived without assuming any cocode identification. -/
theorem pointwiseAxis_octad_sign (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (O : Octad) :
    e.val (xOctad O)=xOctad O ∨ e.val (xOctad O)=-xOctad O := by
  have h := pointwiseAxis_octad_scalar_square e he O
  have hz : (e.val (xOctad O) (.inr O)-1)*(e.val (xOctad O) (.inr O)+1)=0 := by
    linear_combination h
  rcases mul_eq_zero.mp hz with hp | hn
  · left
    rw [pointwiseAxis_octad_line e he O,sub_eq_zero.mp hp,one_smul]
  · right
    have hm : e.val (xOctad O) (.inr O) = -1 := eq_neg_of_add_eq_zero_left hn
    rw [pointwiseAxis_octad_line e he O,hm,neg_one_smul]

end Atlas.Fischer

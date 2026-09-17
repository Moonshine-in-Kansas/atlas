import Atlas.Fischer.DuadOctadicSupports

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Orthogonality for all calibrated character roots over the two actual octads,
proved from their disjoint octad-coordinate supports and the four point regions. -/
theorem duadPair_octadicRoot_orthogonal (F G : Octad) (hFG : (F.val ∩ G.val).card=2)
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (χ : OctadicCharacter F) (ψ : OctadicCharacter G) :
    hermitian (octadicRoot Q χ) (octadicRoot R ψ)=0 := by
  unfold hermitian weightedHermitian
  rw [Fintype.sum_sum_type]
  have ho (D : Octad) : (coordinateWeight (.inr D) : Scalar)*
      octadicRoot Q χ (.inr D)*star (octadicRoot R ψ (.inr D))=0 := by
    rcases duadPair_octadic_octad_coordinate_zero F G hFG Q R χ ψ D with h | h <;> simp [h]
  simp only [ho,Finset.sum_const_zero,add_zero]
  have hi (i : Omega) : (coordinateWeight (.inl i) : Scalar)*
      octadicRoot Q χ (.inl i)*star (octadicRoot R ψ (.inl i))=
      (1/32 : Scalar)-(if i ∈ F.val then 1/16 else 0)-
        (if i ∈ G.val then 1/16 else 0)+(if i ∈ F.val ∩ G.val then 1/8 else 0) := by
    rw [octadicRoot_axis_coefficient,octadicRoot_axis_coefficient]
    by_cases hF : i ∈ F.val <;> by_cases hG : i ∈ G.val <;> norm_num [coordinateWeight,hF,hG]
  rw [Finset.sum_congr rfl (fun i _ => hi i)]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hs (A : Finset Omega) (a : Scalar) :
      (∑ i : Omega, if i ∈ A then a else 0)=(A.card : Scalar)*a := by
    rw [← Finset.sum_filter]
    simp
  rw [hs,hs,hs,octad_size F.val F.property,octad_size G.val G.property,hFG]
  have hc : Fintype.card Omega=24 := by decide
  norm_num [hc]

end Atlas.Fischer

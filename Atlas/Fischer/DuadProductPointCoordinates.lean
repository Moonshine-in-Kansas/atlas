import Atlas.Fischer.DuadProductRoots
import Atlas.Fischer.DuadAxisProduct
import Atlas.Fischer.ProductPointProjection

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The actual duadic product has U_p/8 as its entire point-coordinate part. -/
theorem duadOctadicProduct_axis_coefficient {F G : Octad}
    (hFG : (F.val ∩ G.val).card=2) (Q : OctadCalibration F) (R : OctadCalibration G)
    (χ : OctadicCharacter F) (ψ : OctadicCharacter G) (i : Omega) :
    duadOctadicProduct Q R χ ψ (.inl i)=
      if i ∈ F.val ∩ G.val then (-7/8 : Scalar) else 1/8 := by
  have hx (O : Octad) (S : OctadCalibration O) (η : OctadicCharacter O) (j : Omega) :
      octadicRoot S η (.inl j)=(1/2 : Scalar)*octadicAxisPart O (.inl j) := by
    rw [octadicRoot_axis_coefficient,octadicAxisPart_axis_apply]
    split_ifs <;> ring
  have hu : product (octadicAxisPart F) (octadicAxisPart G) (.inl i)=
      ∑ a : Omega, ∑ b : Omega,
        (star (octadicAxisPart F (.inl a))*star (octadicAxisPart G (.inl b)))*
          axisBasisProduct a b (.inl i) :=
    product_axis_apply_of_octad_disjoint _ _ (fun D => Or.inl (octadicAxisPart_octad_apply F D)) i
  have he : duadOctadicProduct Q R χ ψ (.inl i)=
      (1/4 : Scalar)*product (octadicAxisPart F) (octadicAxisPart G) (.inl i) := by
    rw [duadOctadicProduct,product_axis_apply_of_octad_disjoint _ _
      (duadPair_octadic_octad_coordinate_zero F G hFG Q R χ ψ),hu,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [hx,hx,star_mul,star_mul]
    norm_num only [star_div₀,star_one,star_ofNat]
    ring
  rw [he,product_octadicAxis_duad_pair F G hFG]
  by_cases hi : i ∈ F.val ∩ G.val <;>
    simp [duadicAxisPart,axisSum,Finset.sum_apply,hi] <;> ring

end Atlas.Fischer

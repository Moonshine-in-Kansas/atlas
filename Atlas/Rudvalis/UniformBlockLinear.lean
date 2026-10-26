import Atlas.Rudvalis.BlockAffine

/-! Rank-one bilinear tests force one common linear map in every block. -/
namespace Atlas.Rudvalis

theorem twoPoints_common_one (p q : Point) :
    ∃ u : E, dot u p.val = 1 ∧ dot u q.val = 1 := by
  decide +kernel +revert

theorem matrixAt_add_vector (M : BinaryMatrix) (x y : E) :
    matrixAt M (x+y) = matrixAt M x + matrixAt M y := by
  ext i
  simp [matrixAt,mul_add,Finset.sum_add_distrib]

theorem uniform_block_linear (A : Point → BinaryMatrix)
    (hA : ∀ b u : E, ∃ M : BinaryMatrix, ∀ p : Point,
      dot u p.val • matrixAt (A p).transpose b = matrixAt M p.val) :
    ∀ p q : Point, A p = A q := by
  intro p q
  by_cases hpq : p = q
  · rw [hpq]
  have hpqv : p.val+q.val ≠ 0 := by
    intro h
    apply hpq
    apply Subtype.ext
    have he : p.val+q.val+q.val = q.val := by rw [h,zero_add]
    simpa only [add_assoc,vector_add_self,add_zero] using he
  let r : Point := ⟨p.val+q.val,hpqv⟩
  obtain ⟨u,hup,huq⟩ := twoPoints_common_one p q
  have hur : dot u r.val = 0 := by
    change dot u (p.val+q.val) = 0
    rw [dot_add_right,hup,huq]
    exact Atlas.Codes.bit_self_add _
  have he (b : E) : matrixAt (A p).transpose b = matrixAt (A q).transpose b := by
    obtain ⟨M,hM⟩ := hA b u
    have hp := hM p
    have hq := hM q
    have hr := hM r
    rw [hup,one_smul] at hp
    rw [huq,one_smul] at hq
    rw [hur,zero_smul] at hr
    change 0 = matrixAt M (p.val+q.val) at hr
    rw [matrixAt_add_vector,← hp,← hq] at hr
    have hf := congrArg (fun v : E => v + matrixAt (A q).transpose b) hr
    simpa only [zero_add,add_assoc,vector_add_self,add_zero] using hf.symm
  ext i j
  have hh := congrFun (he (basisPoint i).val) j
  fin_cases i <;> simpa [matrixAt,Matrix.transpose_apply,basisPoint,binaryLabel,Fin.sum_univ_succ] using hh

end Atlas.Rudvalis

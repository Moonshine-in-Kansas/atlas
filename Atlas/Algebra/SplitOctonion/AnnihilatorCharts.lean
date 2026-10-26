import Atlas.Algebra.SplitOctonion.AnnihilatorLinear

/-! Actual four-dimensional annihilators, uniformly over all fields. -/
namespace Atlas.SplitOctonion.Annihilator
variable {F : Type*} [Field F]

def leftAnnihilator (B : Carrier F) : Submodule F (Carrier F) := (multiplication.flip B).ker
def rightAnnihilator (B : Carrier F) : Submodule F (Carrier F) := (multiplication B).ker

noncomputable def leftChart (B : Carrier F) (hB : norm B=0) (i : Fin 8) (hi : B i≠0) :
    Parameters F ≃ₗ[F] leftAnnihilator B where
  toFun a := ⟨(B i)⁻¹ • leftNumeratorLinear B i a,by
    change mul ((B i)⁻¹ • leftNumerator B a i) B=0
    rw [smul_mul,leftNumerator_product,hB,zero_smul,smul_zero]⟩
  invFun A := fun j=>A.val (leftFree i j)
  left_inv a := by
    ext j
    change (B i)⁻¹*leftNumerator B a i (leftFree i j)=a j
    rw [leftNumerator_free,←mul_assoc,inv_mul_cancel₀ hi,one_mul]
  right_inv A := by
    apply Subtype.ext
    change (B i)⁻¹ • leftNumerator B (fun j=>A.val (leftFree i j)) i=A.val
    rw [leftNumerator_reconstruct,show mul A.val B=0 from A.prop,leftCorrection_zero,
      sub_zero,smul_smul,inv_mul_cancel₀ hi,one_smul]
  map_add' a b := by apply Subtype.ext; simp [smul_add]
  map_smul' s a := by
    apply Subtype.ext
    change (B i)⁻¹ • leftNumeratorLinear B i (s • a) = s • ((B i)⁻¹ • leftNumeratorLinear B i a)
    rw [map_smul]
    exact smul_comm _ _ _

noncomputable def rightChart (B : Carrier F) (hB : norm B=0) (i : Fin 8) (hi : B i≠0) :
    Parameters F ≃ₗ[F] rightAnnihilator B where
  toFun c := ⟨(B i)⁻¹ • rightNumeratorLinear B i c,by
    change mul B ((B i)⁻¹ • rightNumerator B c i)=0
    rw [mul_smul,rightNumerator_product,hB,zero_smul,smul_zero]⟩
  invFun C := fun j=>C.val (rightFree i j)
  left_inv c := by
    ext j
    change (B i)⁻¹*rightNumerator B c i (rightFree i j)=c j
    rw [rightNumerator_free,←mul_assoc,inv_mul_cancel₀ hi,one_mul]
  right_inv C := by
    apply Subtype.ext
    change (B i)⁻¹ • rightNumerator B (fun j=>C.val (rightFree i j)) i=C.val
    rw [rightNumerator_reconstruct,show mul B C.val=0 from C.prop,rightCorrection_zero,
      sub_zero,smul_smul,inv_mul_cancel₀ hi,one_smul]
  map_add' a b := by apply Subtype.ext; simp [smul_add]
  map_smul' s a := by
    apply Subtype.ext
    change (B i)⁻¹ • rightNumeratorLinear B i (s • a) = s • ((B i)⁻¹ • rightNumeratorLinear B i a)
    rw [map_smul]
    exact smul_comm _ _ _

theorem exists_nonzero_coordinate (B : Carrier F) (hB : B≠0) : ∃i : Fin 8,B i≠0 := by
  by_contra! h
  exact hB (funext h)

theorem leftAnnihilator_finrank (B : Carrier F) (hB : norm B=0) (hB0 : B≠0) :
    Module.finrank F (leftAnnihilator B)=4 := by
  obtain ⟨i,hi⟩ := exists_nonzero_coordinate B hB0
  rw [←(leftChart B hB i hi).finrank_eq]
  simp [Parameters]

theorem rightAnnihilator_finrank (B : Carrier F) (hB : norm B=0) (hB0 : B≠0) :
    Module.finrank F (rightAnnihilator B)=4 := by
  obtain ⟨i,hi⟩ := exists_nonzero_coordinate B hB0
  rw [←(rightChart B hB i hi).finrank_eq]
  simp [Parameters]

theorem leftAnnihilator_card [Finite F] (B : Carrier F) (hB : norm B=0) (hB0 : B≠0) :
    Nat.card (leftAnnihilator B)=Nat.card F^4 := by
  rw [Module.natCard_eq_pow_finrank (K:=F),leftAnnihilator_finrank B hB hB0]

theorem rightAnnihilator_card [Finite F] (B : Carrier F) (hB : norm B=0) (hB0 : B≠0) :
    Nat.card (rightAnnihilator B)=Nat.card F^4 := by
  rw [Module.natCard_eq_pow_finrank (K:=F),rightAnnihilator_finrank B hB hB0]

theorem norm_of_leftAnnihilator (B : Carrier F) (hB0 : B≠0) (A : leftAnnihilator B) : norm A.val=0 := by
  have h := conjugate_mul_mul A.val B
  rw [show mul A.val B=0 from A.prop] at h
  have hz : norm A.val • B=0 := by
    change multiplication (conjugate A.val) 0 = _ at h
    rw [map_zero] at h
    exact h.symm
  exact (smul_eq_zero.mp hz).resolve_right hB0

theorem norm_of_rightAnnihilator (B : Carrier F) (hB0 : B≠0) (C : rightAnnihilator B) : norm C.val=0 := by
  have h := mul_mul_conjugate B C.val
  rw [show mul B C.val=0 from C.prop] at h
  have hz : norm C.val • B=0 := by
    change multiplication.flip (conjugate C.val) 0 = _ at h
    rw [map_zero] at h
    exact h.symm
  exact (smul_eq_zero.mp hz).resolve_right hB0

end Atlas.SplitOctonion.Annihilator

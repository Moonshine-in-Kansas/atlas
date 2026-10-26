import Atlas.Algebra.SplitOctonion.AnnihilatorCharts

/-! The common annihilator of a nonzero incident pair is a genuine hyperplane
in the four-dimensional right annihilator. No orbit-transitivity assumption is used. -/
noncomputable section
namespace Atlas.SplitOctonion.Annihilator
variable {F : Type*} [Field F]

def commonAnnihilator (A B : Carrier F) : Submodule F (Carrier F) :=
  rightAnnihilator B ⊓ leftAnnihilator A

theorem pivotSign_ne_zero (i : Fin 8) : (pivotSign i : F)≠0 := by
  fin_cases i <;> simp [pivotSign]

theorem chart_pairing (B : Carrier F) (hB : norm B=0) (i : Fin 8) (hi : B i≠0)
    (a c : Parameters F) :
    mul (rightChart B hB i hi c).val (leftChart B hB i hi a).val =
      ((B i)⁻¹*pivotSign i*Atlas.DotProduct.functional (pairCoefficients a i) c) •
        conjugate B := by
  change mul ((B i)⁻¹ • rightNumerator B c i) ((B i)⁻¹ • leftNumerator B a i) = _
  rw [smul_mul,mul_smul,numerator_pairing,hB,zero_smul,add_zero,smul_smul,smul_smul]
  congr 1
  rw [Atlas.DotProduct.functional_apply]
  field_simp [hi]

theorem chart_pairing_eq_zero_iff (B : Carrier F) (hB : norm B=0)
    (i : Fin 8) (hi : B i≠0) (a c : Parameters F) :
    mul (rightChart B hB i hi c).val (leftChart B hB i hi a).val=0 ↔
      Atlas.DotProduct.functional (pairCoefficients a i) c=0 := by
  have hb : B≠0 := by intro h; exact hi (congrFun h i)
  have hc : conjugate B≠0 := by
    intro h
    have hz : conjugate (0 : Carrier F)=0 := by
      ext j; fin_cases j <;> simp [conjugate,trace,unit]
    have he := congrArg conjugate h
    rw [conjugate_conjugate,hz] at he
    exact hb he
  rw [chart_pairing,smul_eq_zero]
  simp [hc,hi,pivotSign_ne_zero]

/-- Explicit hyperplane chart for the actual common annihilator. -/
def commonChart (B : Carrier F) (hB : norm B=0) (i : Fin 8) (hi : B i≠0)
    (a : Parameters F) :
    (Atlas.DotProduct.functional (pairCoefficients a i)).ker ≃ₗ[F]
      commonAnnihilator (leftChart B hB i hi a).val B where
  toFun c := ⟨(rightChart B hB i hi c.val).val,⟨(rightChart B hB i hi c.val).prop,
    (chart_pairing_eq_zero_iff B hB i hi a c.val).mpr c.prop⟩⟩
  invFun C := ⟨(rightChart B hB i hi).symm ⟨C.val,C.prop.1⟩,by
    apply (chart_pairing_eq_zero_iff B hB i hi a _).mp
    have hm : mul C.val (leftChart B hB i hi a).val=0 := C.prop.2
    simpa only [LinearEquiv.apply_symm_apply] using hm⟩
  left_inv c := by apply Subtype.ext; simp
  right_inv C := by apply Subtype.ext; simp
  map_add' c d := by apply Subtype.ext; simp
  map_smul' s c := by apply Subtype.ext; simp

theorem commonAnnihilator_finrank (A B : Carrier F) (hB : norm B=0)
    (hA0 : A≠0) (hB0 : B≠0) (hAB : mul A B=0) :
    Module.finrank F (commonAnnihilator A B)=3 := by
  obtain ⟨i,hi⟩ := exists_nonzero_coordinate B hB0
  let a := (leftChart B hB i hi).symm ⟨A,hAB⟩
  have ha : a≠0 := by
    intro h
    have he := congrArg (leftChart B hB i hi) h
    have hz : (⟨A,hAB⟩ : leftAnnihilator B)=0 := by simpa [a] using he
    exact hA0 (congrArg Subtype.val hz)
  have hcoeff : pairCoefficients a i≠0 := fun h=>ha ((pairCoefficients_eq_zero a i).mp h)
  obtain ⟨v,hv⟩ := Atlas.DotProduct.exists_normalized _ hcoeff
  let l := Atlas.DotProduct.functional (pairCoefficients a i)
  have hr : LinearMap.range l=⊤ := LinearMap.range_eq_top.mpr (by
    intro z
    exact ⟨z • v,by simp [l,map_smul,hv]⟩)
  have hk := l.finrank_range_add_finrank_ker
  rw [hr,finrank_top,Module.finrank_self] at hk
  have hdim : Module.finrank F l.ker=3 := by
    have hn : Module.finrank F (Parameters F)=4 := by simp [Parameters]
    change 1 + Module.finrank F l.ker = Module.finrank F (Parameters F) at hk
    rw [hn] at hk
    omega
  have he := (commonChart B hB i hi a).finrank_eq
  have hea : (leftChart B hB i hi a).val=A :=
    congrArg Subtype.val ((leftChart B hB i hi).apply_symm_apply ⟨A,hAB⟩)
  rw [hea] at he
  exact he.symm.trans hdim

theorem commonAnnihilator_card [Finite F] (A B : Carrier F) (hB : norm B=0)
    (hA0 : A≠0) (hB0 : B≠0) (hAB : mul A B=0) :
    Nat.card (commonAnnihilator A B)=Nat.card F^3 := by
  rw [Module.natCard_eq_pow_finrank (K:=F),commonAnnihilator_finrank A B hB hA0 hB0 hAB]

end Atlas.SplitOctonion.Annihilator

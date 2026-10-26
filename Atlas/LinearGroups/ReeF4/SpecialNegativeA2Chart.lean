import Atlas.LinearGroups.ReeF4.SpecialNegativeC3Chart
import Atlas.LinearGroups.ReeF4.SpecialNegativeA2Pivot

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def negativeA2ChartWord {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (a : F) : Model F m :=
  ⟨weylSigma,weylOperator_mem_modelSubgroup m 1⟩ *
    ⟨longSL2Equiv a (theta F m a),longSL2Parameter_mem_modelSubgroup hcard a⟩

private theorem chart19_sparse (m : ℕ) (z : NormalizedSpecialChart (F := F) m 19) :
    z.val=(z.val.val.2 0 0) • rootVector (F := F) (0,0)+(z.val.val.2 1 0) • rootVector (F := F) (1,0)+
      (z.val.val.2 1 1) • rootVector (F := F) (1,1)+(z.val.val.2 2 0) • rootVector (F := F) (2,0)+rootVector (F := F) (2,1) := by
  have hz0 : z.val.val.1 1=0 := z.property.2.2 0 (by decide)
  have hz1 : z.val.val.1 0=0 := z.property.2.2 1 (by decide)
  have hz3 : z.val.val.2 0 1=0 := z.property.2.2 3 (by decide)
  have hz4 : z.val.val.2 0 2=0 := z.property.2.2 4 (by decide)
  have hz5 : z.val.val.2 0 3=0 := z.property.2.2 5 (by decide)
  have hz6 : z.val.val.2 0 4=0 := z.property.2.2 6 (by decide)
  have hz7 : z.val.val.2 0 5=0 := z.property.2.2 7 (by decide)
  have hz8 : z.val.val.2 0 6=0 := z.property.2.2 8 (by decide)
  have hz9 : z.val.val.2 0 7=0 := z.property.2.2 9 (by decide)
  have hz12 : z.val.val.2 1 2=0 := z.property.2.2 12 (by decide)
  have hz13 : z.val.val.2 1 3=0 := z.property.2.2 13 (by decide)
  have hz14 : z.val.val.2 1 4=0 := z.property.2.2 14 (by decide)
  have hz15 : z.val.val.2 1 5=0 := z.property.2.2 15 (by decide)
  have hz16 : z.val.val.2 1 6=0 := z.property.2.2 16 (by decide)
  have hz17 : z.val.val.2 1 7=0 := z.property.2.2 17 (by decide)
  have hz20 : z.val.val.2 2 2=0 := z.property.2.2 20 (by decide)
  have hz21 : z.val.val.2 2 3=0 := z.property.2.2 21 (by decide)
  have hz22 : z.val.val.2 2 4=0 := z.property.2.2 22 (by decide)
  have hz23 : z.val.val.2 2 5=0 := z.property.2.2 23 (by decide)
  have hz24 : z.val.val.2 2 6=0 := z.property.2.2 24 (by decide)
  have hz25 : z.val.val.2 2 7=0 := z.property.2.2 25 (by decide)
  have hn : z.val.val.2 2 1=1 := z.property.2.1
  have ht := z.val.property
  change z.val.val.1 0+z.val.val.1 1+z.val.val.1 2=0 at ht
  simp only [hz0,hz1,zero_add] at ht
  apply Subtype.ext
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [rootVector,smul_eq_mul,hz0,hz1,ht]
  · funext b j
    fin_cases b <;> fin_cases j <;>
      simp [rootVector,Pi.single_apply,smul_eq_mul,hn,hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25]

def negativeA2ChartInput {m : ℕ} (z : NormalizedSpecialChart (F := F) m 19) : TraceZero F :=
  (z.val.val.2 2 0) • rootVector (F := F) (0,0)+rootVector (F := F) (0,2)+
    (z.val.val.2 1 0) • rootVector (F := F) (1,0)+(z.val.val.2 1 1) • rootVector (F := F) (1,2)+
    (z.val.val.2 0 0) • rootVector (F := F) (2,0)

private theorem chart19_sigma {m : ℕ} (z : NormalizedSpecialChart (F := F) m 19) :
    weylSigma z.val=negativeA2ChartInput z := by
  have hs2 : weylSigma (rootVector (F := F) (0,0))=rootVector (F := F) (2,0) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (0,0)))
  have hs10 : weylSigma (rootVector (F := F) (1,0))=rootVector (F := F) (1,0) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (1,0)))
  have hs11 : weylSigma (rootVector (F := F) (1,1))=rootVector (F := F) (1,2) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (1,1)))
  have hs18 : weylSigma (rootVector (F := F) (2,0))=rootVector (F := F) (0,0) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (2,0)))
  have hs19 : weylSigma (rootVector (F := F) (2,1))=rootVector (F := F) (0,2) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (2,1)))
  calc
    _ = weylSigma ((z.val.val.2 0 0) • rootVector (F := F) (0,0)+(z.val.val.2 1 0) • rootVector (F := F) (1,0)+
      (z.val.val.2 1 1) • rootVector (F := F) (1,1)+(z.val.val.2 2 0) • rootVector (F := F) (2,0)+rootVector (F := F) (2,1)) :=
        congrArg _ (chart19_sparse m z)
    _ = _ := by
      simp only [_root_.map_add,(weylSigma (F := F)).map_smul,hs2,hs10,hs11,hs18,hs19,negativeA2ChartInput]
      abel

/-- The actual nine-coordinate inverse chart; θ(a) is recovered from A−3. -/
def negativeA2ChartPolynomial {m : ℕ} (a : F) (z : NormalizedSpecialChart (F := F) m 19) : TraceZero F :=
  (z.val.val.2 2 0+a*z.val.val.2 0 0) • rootVector (F := F) (0,0)+
    (theta F m a) • rootVector (F := F) (0,1)+rootVector (F := F) (0,2)+
    (z.val.val.2 1 0) • rootVector (F := F) (1,0)+(theta F m a*z.val.val.2 1 1) • rootVector (F := F) (1,1)+
    (z.val.val.2 1 1) • rootVector (F := F) (1,2)+(z.val.val.2 0 0) • rootVector (F := F) (2,0)+
    (a*theta F m a) • rootVector (F := F) (2,1)+a • rootVector (F := F) (2,2)

private theorem negativeA2Chart_shear {m : ℕ} (a : F)
    (z : NormalizedSpecialChart (F := F) m 19) :
    longSL2Equiv a (theta F m a) (negativeA2ChartInput z)=negativeA2ChartPolynomial a z := by
  apply Subtype.ext
  change longSL2Formula a (theta F m a) (negativeA2ChartInput z).val=(negativeA2ChartPolynomial a z).val
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [longSL2Formula,negativeA2ChartInput,negativeA2ChartPolynomial,rootVector,Pi.single_apply,smul_eq_mul]
  · funext b j
    fin_cases b <;> fin_cases j <;>
      simp [longSL2Formula,negativeA2ChartInput,negativeA2ChartPolynomial,rootVector,Pi.single_apply,smul_eq_mul]

theorem negativeA2ChartWord_inverse_formula {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (a : F) (z : NormalizedSpecialChart (F := F) m 19) :
    ((negativeA2ChartWord hcard a)⁻¹).val z.val=negativeA2ChartPolynomial a z := by
  have hL : (longSL2Equiv a (theta F m a))⁻¹=longSL2Equiv a (theta F m a) := by
    apply inv_eq_of_mul_eq_one_left
    simp only [longSL2Equiv_mul,CharTwo.add_self_eq_zero,longSL2Equiv_zero]
  have hS : (weylSigma (F := F))⁻¹=weylSigma := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using weylSigma_square (F := F)
  change ((weylSigma (F := F)) * longSL2Equiv a (theta F m a))⁻¹ z.val=_
  rw [mul_inv_rev,hL,hS]
  change longSL2Equiv a (theta F m a) (weylSigma z.val)=_
  rw [chart19_sigma,negativeA2Chart_shear]

private theorem negativeA2ChartPolynomial_normal {m : ℕ} (a : F)
    (z : NormalizedSpecialChart (F := F) m 19) :
    isotropyCoordinates (negativeA2ChartPolynomial a z) 4=1 := by
  simp [negativeA2ChartPolynomial,isotropyCoordinates,rootVector,Pi.single_apply,smul_eq_mul]

private theorem negativeA2Chart_above_support :
    ∀ j : Fin 26, specialAbsoluteGrade 4 < specialAbsoluteGrade j →
      j ≠ 2 ∧ j ≠ 3 ∧ j ≠ 4 ∧ j ≠ 10 ∧ j ≠ 11 ∧ j ≠ 12 ∧ j ≠ 18 ∧ j ≠ 19 ∧ j ≠ 20 := by decide

private theorem negativeA2ChartPolynomial_upper {m : ℕ} (a : F)
    (z : NormalizedSpecialChart (F := F) m 19) :
    ∀ j, specialAbsoluteGrade 4<specialAbsoluteGrade j →
      isotropyCoordinates (negativeA2ChartPolynomial a z) j=0 := by
  intro j hj
  obtain ⟨h2,h3,h4,h10,h11,h12,h18,h19,h20⟩ := negativeA2Chart_above_support j hj
  fin_cases j <;>
    simp_all [negativeA2ChartPolynomial,isotropyCoordinates,rootVector,Pi.single_apply,smul_eq_mul]

def negativeA2ChartEncode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F × NormalizedSpecialChart (F := F) m 19) : NormalizedSpecialChart (F := F) m 4 :=
  ⟨((negativeA2ChartWord hcard p.1)⁻¹).val p.2.val,p.2.property.1.map_model ((negativeA2ChartWord hcard p.1)⁻¹),by
    rw [negativeA2ChartWord_inverse_formula]
    exact negativeA2ChartPolynomial_normal _ _,by
    rw [negativeA2ChartWord_inverse_formula]
    exact negativeA2ChartPolynomial_upper _ _⟩

def negativeA2ChartParameter {m : ℕ} (u : NormalizedSpecialChart (F := F) m 4) : F :=
  negativeA2PivotParameter m u.val

theorem negativeA2ChartParameter_encode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F × NormalizedSpecialChart (F := F) m 19) :
    negativeA2ChartParameter (negativeA2ChartEncode hcard p)=p.1 := by
  have he : (negativeA2ChartEncode hcard p).val=negativeA2ChartPolynomial p.1 p.2 :=
    negativeA2ChartWord_inverse_formula hcard p.1 p.2
  change negativeA2PivotParameter m (negativeA2ChartEncode hcard p).val = p.1
  rw [he]
  unfold negativeA2PivotParameter
  have hAm3 : (negativeA2ChartPolynomial p.1 p.2).val.2 0 1=theta F m p.1 := by
    simp [negativeA2ChartPolynomial,rootVector,Pi.single_apply,smul_eq_mul]
  have hAm2 : (negativeA2ChartPolynomial p.1 p.2).val.2 0 2=1 := by
    simp [negativeA2ChartPolynomial,rootVector,Pi.single_apply,smul_eq_mul]
  rw [hAm3,hAm2,div_one,thetaInv_theta hcard]

def negativeA2ChartDecode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : NormalizedSpecialChart (F := F) m 4) : F × NormalizedSpecialChart (F := F) m 19 :=
  (negativeA2ChartParameter u,⟨(negativeA2PivotDescent hcard u.val).val u.val,by
    have hc : u.val.val.2 0 2≠0 := by
      have he : u.val.val.2 0 2=1 := u.property.2.1
      rw [he]; exact one_ne_zero
    obtain ⟨hs,he,hz⟩ := specialVector_negativeA2_descent hcard u.property.1 u.property.2.2 hc
    refine ⟨hs,?_,hz⟩
    change ((negativeA2PivotDescent hcard u.val).val u.val).val.2 2 1=1
    exact he.trans u.property.2.1⟩)

private theorem negativeA2ChartDecode_lower {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : NormalizedSpecialChart (F := F) m 4) :
    (negativeA2ChartDecode hcard u).2.val=
      (negativeA2ChartWord hcard (negativeA2ChartParameter u)).val u.val := by
  have he : negativeA2PivotDescent hcard u.val =
      negativeA2ChartWord hcard (negativeA2ChartParameter u) := by
    apply Subtype.ext
    rfl
  dsimp only [negativeA2ChartDecode]
  rw [he]

def normalizedChart4Equiv {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    NormalizedSpecialChart (F := F) m 4 ≃ F × NormalizedSpecialChart (F := F) m 19 where
  toFun := negativeA2ChartDecode hcard
  invFun := negativeA2ChartEncode hcard
  left_inv u := by
    apply Subtype.ext
    change ((negativeA2ChartWord hcard (negativeA2ChartParameter u))⁻¹).val
      ((negativeA2ChartDecode hcard u).2.val)=u.val
    rw [negativeA2ChartDecode_lower]
    exact (negativeA2ChartWord hcard (negativeA2ChartParameter u)).val.symm_apply_apply u.val
  right_inv p := by
    apply Prod.ext
    · exact negativeA2ChartParameter_encode hcard p
    · apply Subtype.ext
      rw [negativeA2ChartDecode_lower,negativeA2ChartParameter_encode]
      change (negativeA2ChartWord hcard p.1).val (negativeA2ChartEncode hcard p).val = p.2.val
      have hv : (negativeA2ChartEncode hcard p).val =
          ((negativeA2ChartWord hcard p.1)⁻¹).val p.2.val := rfl
      rw [hv]
      exact chart_model_apply_inv (negativeA2ChartWord hcard p.1) p.2.val

theorem card_normalizedChart4 {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (NormalizedSpecialChart (F := F) m 4)=(Nat.card F)^4 := by
  rw [Nat.card_congr (normalizedChart4Equiv hcard),Nat.card_prod,card_normalizedChart19 hcard]
  ring
end Atlas.ReeF4

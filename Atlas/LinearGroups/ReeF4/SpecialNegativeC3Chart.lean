import Atlas.LinearGroups.ReeF4.SpecialLowestCharts
import Atlas.LinearGroups.ReeF4.SpecialNegativeC3Pivot
import Atlas.LinearGroups.ReeF4.WeylSupport

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem chart_model_apply_inv {m : ℕ} (g : Model F m) (u : TraceZero F) :
    g.val ((g⁻¹).val u) = u := g.val.apply_symm_apply u

/-- The actual forward pivot word, with independent parameters. -/
def negativeC3ChartWord {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (p : F×F) : Model F m :=
  ⟨weylRho,weylOperator_mem_modelSubgroup m 0⟩ *
    ⟨shortRootPairEquiv m hcard p.1 p.2,shortRootPairEquiv_mem_modelSubgroup hcard _ _⟩

/-- Five-term normal form of the inverse pivot on the normalized lower chart.
The correction b+aθ(a) belongs to the actual root-group inverse. -/
def negativeC3ChartPolynomial (m : ℕ) (a b c : F) : TraceZero F :=
  let d := b+a*theta F m a
  c • rootVector (F := F) (0,0)+d • rootVector (F := F) (1,0)+a • rootVector (F := F) (1,1)+
    (theta F m d+a*d+a^2*theta F m a) • rootVector (F := F) (2,0)+rootVector (F := F) (2,1)

private theorem negativeC3Pair_on_lowest {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (a d : F) :
    shortRootPairEquiv m hcard a d (rootVector (F := F) (0,0))=rootVector (F := F) (0,0) := by
  apply Subtype.ext
  change shortRootParameterFormula (theta F m).toRingHom a
    (shortRootCenterFormula (theta F m).toRingHom d (rootVector (F := F) (0,0)).val)=_
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [shortRootParameterFormula,shortRootCenterFormula,rootVector,Pi.single_apply]
  · funext b j
    fin_cases b <;> fin_cases j <;>
      simp [shortRootParameterFormula,shortRootCenterFormula,rootVector,Pi.single_apply]

private theorem negativeC3Pair_on_Cm3 {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (a d : F) :
    shortRootPairEquiv m hcard a d (rootVector (F := F) (2,1))=
      d • rootVector (F := F) (1,0)+a • rootVector (F := F) (1,1)+
      (theta F m d+a*d+a^2*theta F m a) • rootVector (F := F) (2,0)+rootVector (F := F) (2,1) := by
  apply Subtype.ext
  change shortRootParameterFormula (theta F m).toRingHom a
    (shortRootCenterFormula (theta F m).toRingHom d (rootVector (F := F) (2,1)).val)=_
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [shortRootParameterFormula,shortRootCenterFormula,rootVector,Pi.single_apply,smul_eq_mul]
  · funext b j
    fin_cases b <;> fin_cases j <;>
      simp [shortRootParameterFormula,shortRootCenterFormula,rootVector,Pi.single_apply,smul_eq_mul]

/-- Actual inverse-word formula, before any cardinality or chart bijection. -/
theorem negativeC3ChartWord_inverse_formula {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F×F) (z : NormalizedSpecialChart (F := F) m 18) :
    ((negativeC3ChartWord hcard p)⁻¹).val z.val=
      negativeC3ChartPolynomial m p.1 p.2 (z.val.val.2 0 0) := by
  have hA : weylRho (rootVector (F := F) (0,0))=rootVector (F := F) (0,0) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 0 (.inr (0,0)))
  have hC : weylRho (rootVector (F := F) (2,0))=rootVector (F := F) (2,1) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 0 (.inr (2,0)))
  have hrho : (weylRho (F := F))⁻¹=weylRho := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using weylRho_square (F := F)
  change ((shortRootPairEquiv m hcard p.1 p.2)⁻¹ * (weylRho (F := F))⁻¹) z.val=_
  rw [hrho,shortRootPairEquiv_inv]
  change shortRootPairEquiv m hcard p.1 (p.2+p.1*theta F m p.1) (weylRho z.val)=_
  have hz : weylRho z.val=(z.val.val.2 0 0) • rootVector (F := F) (0,0)+rootVector (F := F) (2,1) := by
    calc
      _ = weylRho ((z.val.val.2 0 0) • rootVector (F := F) (0,0)+rootVector (F := F) (2,0)) :=
        congrArg _ (normalizedChart18_eq_sum z)
      _ = _ := by rw [_root_.map_add,(weylRho (F := F)).map_smul,hA,hC]
  rw [hz,_root_.map_add,(shortRootPairEquiv m hcard p.1 (p.2+p.1*theta F m p.1)).map_smul,
    negativeC3Pair_on_lowest,negativeC3Pair_on_Cm3]
  simp only [negativeC3ChartPolynomial]
  abel

private theorem negativeC3ChartPolynomial_normal (m : ℕ) (a b c : F) :
    isotropyCoordinates (negativeC3ChartPolynomial m a b c) 19=1 := by
  simp [negativeC3ChartPolynomial,isotropyCoordinates,rootVector,Pi.single_apply,smul_eq_mul]

private theorem negativeC3Chart_above_support :
    ∀ j : Fin 26, specialAbsoluteGrade 19 < specialAbsoluteGrade j →
      j ≠ 2 ∧ j ≠ 10 ∧ j ≠ 11 ∧ j ≠ 18 ∧ j ≠ 19 := by decide

private theorem negativeC3ChartPolynomial_upper (m : ℕ) (a b c : F) :
    ∀ j, specialAbsoluteGrade 19<specialAbsoluteGrade j →
      isotropyCoordinates (negativeC3ChartPolynomial m a b c) j=0 := by
  intro j hj
  obtain ⟨h2,h10,h11,h18,h19⟩ := negativeC3Chart_above_support j hj
  fin_cases j <;>
    simp_all [negativeC3ChartPolynomial,isotropyCoordinates,rootVector,Pi.single_apply,smul_eq_mul]

/-- Reverse any two parameters and any normalized lower-chart vector. -/
def negativeC3ChartEncode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : (F×F) × NormalizedSpecialChart (F := F) m 18) : NormalizedSpecialChart (F := F) m 19 :=
  ⟨((negativeC3ChartWord hcard p.1)⁻¹).val p.2.val,p.2.property.1.map_model ((negativeC3ChartWord hcard p.1)⁻¹),by
    rw [negativeC3ChartWord_inverse_formula]
    exact negativeC3ChartPolynomial_normal _ _ _ _,by
    rw [negativeC3ChartWord_inverse_formula]
    exact negativeC3ChartPolynomial_upper _ _ _ _⟩

def negativeC3ChartParameters {m : ℕ} (u : NormalizedSpecialChart (F := F) m 19) : F×F :=
  (negativeC3PivotA u.val,negativeC3PivotB m u.val)

theorem negativeC3ChartParameters_encode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : (F×F) × NormalizedSpecialChart (F := F) m 18) :
    negativeC3ChartParameters (negativeC3ChartEncode hcard p)=p.1 := by
  have he : (negativeC3ChartEncode hcard p).val=
      negativeC3ChartPolynomial m p.1.1 p.1.2 (p.2.val.val.2 0 0) :=
    negativeC3ChartWord_inverse_formula hcard p.1 p.2
  change (negativeC3PivotA (negativeC3ChartEncode hcard p).val,
    negativeC3PivotB m (negativeC3ChartEncode hcard p).val) = p.1
  rw [he]
  apply Prod.ext
  · simp [negativeC3PivotA,negativeC3ChartPolynomial,rootVector,Pi.single_apply,smul_eq_mul]
  · simp [negativeC3PivotB,negativeC3PivotA,negativeC3ChartPolynomial,rootVector,Pi.single_apply,smul_eq_mul]
    -- The sole scalar cancellation is b+aθ(a)+θ(a)a=b in characteristic2.
    all_goals ring_nf
    all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]

/-- Forward reduction retaining both independently recoverable parameters. -/
def negativeC3ChartDecode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : NormalizedSpecialChart (F := F) m 19) :
    (F×F) × NormalizedSpecialChart (F := F) m 18 :=
  (negativeC3ChartParameters u,⟨(negativeC3PivotDescent hcard u.val).val u.val,by
    have hc : u.val.val.2 2 1≠0 := by
      have he : u.val.val.2 2 1=1 := u.property.2.1
      rw [he]; exact one_ne_zero
    obtain ⟨hs,he,hz⟩ := specialVector_negativeC3_descent hcard u.property.1 u.property.2.2 hc
    refine ⟨hs,?_,hz⟩
    change ((negativeC3PivotDescent hcard u.val).val u.val).val.2 2 0=1
    exact he.trans u.property.2.1⟩)

private theorem negativeC3ChartDecode_lower {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : NormalizedSpecialChart (F := F) m 19) :
    (negativeC3ChartDecode hcard u).2.val=
      (negativeC3ChartWord hcard (negativeC3ChartParameters u)).val u.val := by
  have he : negativeC3PivotDescent hcard u.val =
      negativeC3ChartWord hcard (negativeC3ChartParameters u) := by
    apply Subtype.ext
    rfl
  dsimp only [negativeC3ChartDecode]
  rw [he]

/-- The third genuine affine chart adds precisely two independent parameters. -/
def normalizedChart19Equiv {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    NormalizedSpecialChart (F := F) m 19 ≃ (F×F) × NormalizedSpecialChart (F := F) m 18 where
  toFun := negativeC3ChartDecode hcard
  invFun := negativeC3ChartEncode hcard
  left_inv u := by
    apply Subtype.ext
    change ((negativeC3ChartWord hcard (negativeC3ChartParameters u))⁻¹).val
      ((negativeC3ChartDecode hcard u).2.val)=u.val
    rw [negativeC3ChartDecode_lower]
    exact (negativeC3ChartWord hcard (negativeC3ChartParameters u)).val.symm_apply_apply u.val
  right_inv p := by
    apply Prod.ext
    · exact negativeC3ChartParameters_encode hcard p
    · apply Subtype.ext
      rw [negativeC3ChartDecode_lower,negativeC3ChartParameters_encode]
      change (negativeC3ChartWord hcard p.1).val (negativeC3ChartEncode hcard p).val = p.2.val
      have hv : (negativeC3ChartEncode hcard p).val =
          ((negativeC3ChartWord hcard p.1)⁻¹).val p.2.val := rfl
      rw [hv]
      exact chart_model_apply_inv (negativeC3ChartWord hcard p.1) p.2.val

theorem card_normalizedChart19 {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (NormalizedSpecialChart (F := F) m 19)=(Nat.card F)^3 := by
  rw [Nat.card_congr (normalizedChart19Equiv hcard),Nat.card_prod,Nat.card_prod,card_normalizedChart18 hcard]
  ring
end Atlas.ReeF4

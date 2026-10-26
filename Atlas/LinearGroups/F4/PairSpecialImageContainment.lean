import Atlas.LinearGroups.F4.PairQuotientKernel
import Atlas.LinearGroups.F4.LeviSpecialImage
import Atlas.LinearGroups.F4.RadicalQuotientKernel
import Atlas.LinearGroups.F4.PairStabilizerScales

/-! Exclusion of the determinant-minus component by the actual lower-spin
intertwining equations. No order or recognition theorem for F₄ is involved. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def quotientAnisotropicReflection : Atlas.Orthogonal.O_B 3 F :=
  Atlas.Orthogonal.reflectionElement (Atlas.Orthogonal.formB 3 F) (0,1)
    (by simp [Atlas.Orthogonal.formD_apply])

theorem quotientAnisotropicReflection_apply (v : Atlas.Orthogonal.VectorB 3 F) :
    (quotientAnisotropicReflection (F:=F)).val v=(v.1,-v.2) := by
  change Atlas.Quadratic.reflectionLinear (Atlas.Orthogonal.formB 3 F) (0,1)
    (by simp [Atlas.Orthogonal.formD_apply]) v=_
  rw [Atlas.Quadratic.reflectionLinear_apply]
  apply Prod.ext
  · ext i
    simp [QuadraticMap.polar,Atlas.Orthogonal.formD_apply]
  · simp [QuadraticMap.polar,Atlas.Orthogonal.formD_apply]
    ring

def middleReflectionVector (v : SplitOctonion.Carrier F) : SplitOctonion.Carrier F :=
  ![v 0,v 1,v 2,v 4,v 3,v 5,v 6,v 7]

theorem pairReflection_middle_traceZero (g : parabolicPointStabilizer (F:=F)) (t : Fˣ)
    (hp : g.val.val parabolicVector=t.val • parabolicVector)
    (hq : g.val.val pairOppositeVector=(t⁻¹).val • pairOppositeVector)
    (hr : parabolicOrthogonalHom g=quotientAnisotropicReflection)
    (v : SplitOctonion.Carrier F) (hv : SplitOctonion.trace v=0) :
    middleOctRestriction g.val t hp hq v=middleReflectionVector v := by
  apply middleOct_seven_trace_injective
  · let x : parabolicCrossTrace (F:=F) := ⟨middleOctEmbed v,middleOct_mem_crossTrace v hv⟩
    have he := parabolicSevenEquiv_apply g x
    have h7 : parabolicSevenEquiv g=(quotientAnisotropicReflection (F:=F)).val :=
      congrArg Subtype.val hr
    rw [h7,quotientAnisotropicReflection_apply] at he
    change ((parabolicSevenCoordinates (middleOctEmbed v)).1,
      -(parabolicSevenCoordinates (middleOctEmbed v)).2)=
        parabolicSevenCoordinates (g.val.val (middleOctEmbed v)) at he
    change parabolicSevenCoordinates (middleOctEmbed (middleOctRestrictionMap g.val v))=_
    rw [middleOctRestrictionMap_embed g.val t hp hq,←he]
    apply Prod.ext
    · ext i; cases i with
      | inl i => fin_cases i <;> rfl
      | inr i => fin_cases i <;> rfl
    · change -v 3=v 4
      change v 3+v 4=0 at hv
      linear_combination -hv
  · rw [middleOctRestriction_trace]
    simp [SplitOctonion.trace,middleReflectionVector,add_comm]

theorem pairReflection_lower_commutes (g : parabolicPointStabilizer (F:=F)) (t : Fˣ)
    (hp : g.val.val parabolicVector=t.val • parabolicVector)
    (hq : g.val.val pairOppositeVector=(t⁻¹).val • pairOppositeVector)
    (hr : parabolicOrthogonalHom g=quotientAnisotropicReflection)
    (i : Fin 6) (v : LowerSpinSpace F) :
    lowerSpinRestriction g.val t hp hq (lowerSpinOperator i v)=
      lowerSpinOperator i (lowerSpinRestriction g.val t hp hq v) := by
  have h := pairSpin_intertwining g.val t hp hq (middleOperatorParameter i) v
  rw [pairReflection_middle_traceZero g t hp hq hr _ (middleOperatorParameter_trace i)] at h
  have hm : middleReflectionVector (middleOperatorParameter (F:=F) i)=middleOperatorParameter i := by
    fin_cases i <;> ext j <;> fin_cases j <;>
      simp [middleReflectionVector,middleOperatorParameter,SplitOctonion.basisVector,Pi.single_apply]
  rw [hm,middleOperatorParameter_action,middleOperatorParameter_action] at h
  exact h

/-- A pair stabilizer cannot induce the anisotropic reflection in odd characteristic. -/
theorem pair_no_anisotropic_reflection (h2 : (2:F)≠0)
    (g : parabolicPointStabilizer (F:=F)) (t : Fˣ)
    (hp : g.val.val parabolicVector=t.val • parabolicVector)
    (hq : g.val.val pairOppositeVector=(t⁻¹).val • pairOppositeVector)
    (hr : parabolicOrthogonalHom g=quotientAnisotropicReflection) : False := by
  let G := middleOctRestriction g.val t hp hq
  have hu : G (SplitOctonion.basisVector 3)+G (SplitOctonion.basisVector 4)=
      SplitOctonion.basisVector 3+SplitOctonion.basisVector 4 := by
    have he : (SplitOctonion.unit : SplitOctonion.Carrier F)=
        SplitOctonion.basisVector 3+SplitOctonion.basisVector 4 := by
      ext i; fin_cases i <;> simp [SplitOctonion.unit,SplitOctonion.basisVector,Pi.single_apply]
    have h := middleOctRestriction_unit g.val t hp hq
    rw [he,_root_.map_add] at h
    exact h
  have hd : G (SplitOctonion.basisVector 3)-G (SplitOctonion.basisVector 4)=
      SplitOctonion.basisVector 4-SplitOctonion.basisVector 3 := by
    have h := pairReflection_middle_traceZero g t hp hq hr
      (SplitOctonion.basisVector 3-SplitOctonion.basisVector 4)
      (by simp [SplitOctonion.trace,SplitOctonion.basisVector,Pi.single_apply])
    rw [map_sub] at h
    have he : middleReflectionVector (SplitOctonion.basisVector 3-SplitOctonion.basisVector 4 :
        SplitOctonion.Carrier F)=SplitOctonion.basisVector 4-SplitOctonion.basisVector 3 := by
      ext i; fin_cases i <;> simp [middleReflectionVector,SplitOctonion.basisVector,Pi.single_apply]
    rw [he] at h
    exact h
  have hg3 : G (SplitOctonion.basisVector 3)=SplitOctonion.basisVector 4 := by
    ext i
    apply mul_left_cancel₀ h2
    have h₁ := congrFun hu i
    have h₂ := congrFun hd i
    simp only [Pi.add_apply,Pi.sub_apply] at h₁ h₂
    linear_combination h₁+h₂
  have hs : ∀ v, lowerSpinRestriction g.val t hp hq (lowerSpinAction 1 0 0 v)=
      lowerSpinAction 0 1 0 (lowerSpinRestriction g.val t hp hq v) := by
    intro v
    have h := pairSpin_intertwining g.val t hp hq (SplitOctonion.basisVector 3) v
    change lowerSpinRestriction g.val t hp hq (middleLowerAction (SplitOctonion.basisVector 3) v)=
      middleLowerAction (G (SplitOctonion.basisVector 3)) (lowerSpinRestriction g.val t hp hq v) at h
    rw [hg3] at h
    have hz : (![0,0,0,0,0,0] : Fin 6 → F)=0 := by
      ext i; fin_cases i <;> rfl
    simpa [middleLowerAction,SplitOctonion.basisVector,Pi.single_apply,hz] using h
  exact lowerSpinOperator_no_diagonal_swap
    (lowerSpinRestriction g.val t hp hq).toLinearMap
    (lowerSpinRestriction g.val t hp hq).injective
    (pairReflection_lower_commutes g t hp hq hr) hs


set_option maxHeartbeats 600000 in
-- Keep the nested actual stabilizer homomorphisms opaque during the coset correction.
/-- The quotient image has no determinant-minus component. -/
theorem pairOrthogonalHom_range_le_special [Finite F] :
    (pairOrthogonalHom (F:=F)).range ≤ Atlas.Orthogonal.specialSubgroup (Atlas.Orthogonal.formB 3 F) := by
  rintro _ ⟨g,rfl⟩
  by_cases h2 : (2:F)=0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    rw [Atlas.Orthogonal.even_specialB_eq_top]
    trivial
  have hsq := Atlas.Quadratic.isometry_det_sq (Atlas.Orthogonal.formB 3 F)
    (Atlas.Orthogonal.polarB_nondegenerate h2)
    (Atlas.Orthogonal.isometryCarrierEquiv _ (pairOrthogonalHom g))
  change ((pairOrthogonalHom g).val.det:F)^2=1 at hsq
  rcases sq_eq_one_iff.mp hsq with hd | hd
  · apply Units.ext
    exact hd
  exfalso
  let s := pairOrthogonalHom g*quotientAnisotropicReflection (F:=F)
  have hs : s∈Atlas.Orthogonal.specialSubgroup (Atlas.Orthogonal.formB 3 F) := by
    change Atlas.Orthogonal.determinant (Atlas.Orthogonal.formB 3 F)
      (pairOrthogonalHom g*quotientAnisotropicReflection)=1
    rw [map_mul]
    have hr : Atlas.Orthogonal.determinant (Atlas.Orthogonal.formB 3 F)
        quotientAnisotropicReflection=(-1:Fˣ) :=
      Atlas.Orthogonal.reflectionElement_determinant _ _ _
    rw [hr]
    apply Units.ext
    change ((pairOrthogonalHom g).val.det:F)*(-1)=1
    rw [hd]
    ring
  have hm : s∈(pairOrthogonalHom (F:=F)).range := by
    rw [pairOrthogonalHom_range_eq]
    exact specialB3_le_parabolic_image hs
  obtain ⟨l,hl⟩ := hm
  have hr : pairOrthogonalHom (l⁻¹*g)=quotientAnisotropicReflection := by
    rw [map_mul,map_inv,hl]
    dsimp only [s]
    simp only [mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one]
    exact Atlas.Orthogonal.reflectionElement_inv _ _ _
  exact pair_no_anisotropic_reflection h2 (l⁻¹*g).val
    (parabolicLineCharacter (l⁻¹*g).val)
    (pairStabilizer_positive_scale (l⁻¹*g)) (pairStabilizer_opposite_scale (l⁻¹*g)) hr

/-- Actual equality of the seven-dimensional quotient image with the special
orthogonal group, obtained structurally in every finite characteristic. -/
theorem pairOrthogonalHom_range_eq_special [Finite F] :
    (pairOrthogonalHom (F:=F)).range=Atlas.Orthogonal.specialSubgroup (Atlas.Orthogonal.formB 3 F) := by
  apply le_antisymm pairOrthogonalHom_range_le_special
  rw [pairOrthogonalHom_range_eq]
  exact specialB3_le_parabolic_image

theorem parabolicOrthogonalHom_range_eq_special [Finite F] :
    (parabolicOrthogonalHom (F:=F)).range=Atlas.Orthogonal.specialSubgroup (Atlas.Orthogonal.formB 3 F) := by
  rw [←pairOrthogonalHom_range_eq]
  exact pairOrthogonalHom_range_eq_special

end Atlas.F4

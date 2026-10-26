import Atlas.LinearGroups.F4.PairSpinRestrictions
import Atlas.LinearGroups.F4.ParabolicQuotientAction
import Atlas.Algebra.SplitOctonion.TraceKernelIsometry

/-! Actual consequences of being in the seven-dimensional quotient-action kernel:
the middle eight-space is fixed and the lower eight-space action is scalar.
The characteristic-two residual swap is excluded by the actual cross operators. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

theorem middleOctEmbed_trace (v : SplitOctonion.Carrier F) :
    trace (middleOctEmbed v)=SplitOctonion.trace v := by
  simp [trace,middleOctEmbed,middleSpinEmbed,SplitOctonion.trace]

theorem middleOctRestriction_trace (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector)
    (v : SplitOctonion.Carrier F) :
    SplitOctonion.trace (middleOctRestriction g t hp hq v)=SplitOctonion.trace v := by
  rw [←middleOctEmbed_trace,←middleOctEmbed_trace v]
  change trace (middleOctEmbed (middleOctRestrictionMap g v))=_
  rw [middleOctRestrictionMap_embed g t hp hq,stabilizer_trace]

theorem middleOct_seven_trace_injective (v w : SplitOctonion.Carrier F)
    (h : parabolicSevenCoordinates (middleOctEmbed v)=parabolicSevenCoordinates (middleOctEmbed w))
    (ht : SplitOctonion.trace v=SplitOctonion.trace w) : v=w := by
  have h0 := congrArg (fun x : Atlas.Orthogonal.VectorB 3 F=>x.1 (.inl 0)) h
  have h1 := congrArg (fun x : Atlas.Orthogonal.VectorB 3 F=>x.1 (.inl 1)) h
  have h2 := congrArg (fun x : Atlas.Orthogonal.VectorB 3 F=>x.1 (.inl 2)) h
  have h3 := congrArg Prod.snd h
  have h5 := congrArg (fun x : Atlas.Orthogonal.VectorB 3 F=>x.1 (.inr 2)) h
  have h6 := congrArg (fun x : Atlas.Orthogonal.VectorB 3 F=>x.1 (.inr 1)) h
  have h7 := congrArg (fun x : Atlas.Orthogonal.VectorB 3 F=>x.1 (.inr 0)) h
  simp [parabolicSevenCoordinates,middleOctEmbed,middleSpinEmbed] at h0 h1 h2 h3 h5 h6 h7
  have h4 : v 4=w 4 := by
    change v 3+v 4=w 3+w 4 at ht
    linear_combination ht-h3
  ext i; fin_cases i <;> assumption

theorem middleOct_mem_crossTrace (v : SplitOctonion.Carrier F)
    (hv : SplitOctonion.trace v=0) : middleOctEmbed v∈parabolicCrossTrace (F:=F) := by
  refine ⟨(parabolicCross_eq_zero_iff _).mpr ?_,?_⟩
  · simp [middleOctEmbed,middleSpinEmbed]
  · change trace (middleOctEmbed v)=0
    rw [middleOctEmbed_trace,hv]

theorem pairKernel_middle_traceZero (g : parabolicPointStabilizer (F:=F)) (t : Fˣ)
    (hp : g.val.val parabolicVector=t.val • parabolicVector)
    (hq : g.val.val pairOppositeVector=(t⁻¹).val • pairOppositeVector)
    (hker : parabolicOrthogonalHom g=1) (v : SplitOctonion.Carrier F)
    (hv : SplitOctonion.trace v=0) : middleOctRestriction g.val t hp hq v=v := by
  apply middleOct_seven_trace_injective
  · let x : parabolicCrossTrace (F:=F) := ⟨middleOctEmbed v,middleOct_mem_crossTrace v hv⟩
    have he := parabolicSevenEquiv_apply g x
    have h7 : parabolicSevenEquiv g=1 := congrArg Subtype.val hker
    rw [h7] at he
    change parabolicSevenCoordinates (middleOctEmbed v)=
      parabolicSevenCoordinates (g.val.val (middleOctEmbed v)) at he
    change parabolicSevenCoordinates (middleOctEmbed (middleOctRestrictionMap g.val v))=_
    rw [middleOctRestrictionMap_embed g.val t hp hq]
    exact he.symm
  · exact middleOctRestriction_trace g.val t hp hq v

def middleOperatorParameter (i : Fin 6) : SplitOctonion.Carrier F :=
  ![SplitOctonion.basisVector 0,SplitOctonion.basisVector 1,SplitOctonion.basisVector 2,
    -SplitOctonion.basisVector 5,-SplitOctonion.basisVector 6,-SplitOctonion.basisVector 7] i

theorem middleOperatorParameter_trace (i : Fin 6) :
    SplitOctonion.trace (middleOperatorParameter (F:=F) i)=0 := by
  fin_cases i <;> simp [middleOperatorParameter,SplitOctonion.trace,SplitOctonion.basisVector]

theorem middleOperatorParameter_action (i : Fin 6) (v : LowerSpinSpace F) :
    middleLowerAction (middleOperatorParameter i) v=lowerSpinOperator i v := by
  ext j; fin_cases i <;> fin_cases j <;>
    simp [middleLowerAction,middleOperatorParameter,lowerSpinAction,lowerSpinOperator,
      lowerSpinOperatorValue,SplitOctonion.basisVector,Pi.single_apply]

theorem pairKernel_lower_commutes (g : parabolicPointStabilizer (F:=F)) (t : Fˣ)
    (hp : g.val.val parabolicVector=t.val • parabolicVector)
    (hq : g.val.val pairOppositeVector=(t⁻¹).val • pairOppositeVector)
    (hker : parabolicOrthogonalHom g=1) (i : Fin 6) (v : LowerSpinSpace F) :
    lowerSpinRestriction g.val t hp hq (lowerSpinOperator i v)=
      lowerSpinOperator i (lowerSpinRestriction g.val t hp hq v) := by
  have h := pairSpin_intertwining g.val t hp hq (middleOperatorParameter i) v
  rw [pairKernel_middle_traceZero g t hp hq hker _ (middleOperatorParameter_trace i),
    middleOperatorParameter_action,middleOperatorParameter_action] at h
  exact h

theorem pairKernel_lower_scalar (g : parabolicPointStabilizer (F:=F)) (t : Fˣ)
    (hp : g.val.val parabolicVector=t.val • parabolicVector)
    (hq : g.val.val pairOppositeVector=(t⁻¹).val • pairOppositeVector)
    (hker : parabolicOrthogonalHom g=1) :
    ∃ c : F, c≠0 ∧ ∀ v, lowerSpinRestriction g.val t hp hq v=c • v := by
  obtain ⟨c,hc⟩ := lowerSpinOperator_centralizer
    (lowerSpinRestriction g.val t hp hq).toLinearMap (pairKernel_lower_commutes g t hp hq hker)
  change ∀ v, lowerSpinRestriction g.val t hp hq v=c • v at hc
  refine ⟨c,?_,hc⟩
  intro hc0
  have he : lowerSpinRestriction g.val t hp hq lowerSpinVacuum=
      lowerSpinRestriction g.val t hp hq 0 := by
    rw [hc,hc,hc0]
    simp
  have hz := congrFun ((lowerSpinRestriction g.val t hp hq).injective he) 0
  simpa [lowerSpinVacuum,Pi.single_apply] using hz

theorem pairKernel_middle_identity (g : parabolicPointStabilizer (F:=F)) (t : Fˣ)
    (hp : g.val.val parabolicVector=t.val • parabolicVector)
    (hq : g.val.val pairOppositeVector=(t⁻¹).val • pairOppositeVector)
    (hker : parabolicOrthogonalHom g=1) (v : SplitOctonion.Carrier F) :
    middleOctRestriction g.val t hp hq v=v := by
  rcases SplitOctonion.normIsometry_traceKernel (middleOctRestriction g.val t hp hq)
    (middleOctRestriction_norm g.val t hp hq)
    (pairKernel_middle_traceZero g t hp hq hker) with hid | hneg
  · exact hid v
  · exfalso
    have hswap : ∀ w, lowerSpinRestriction g.val t hp hq (lowerSpinAction 1 0 0 w)=
        lowerSpinAction 0 1 0 (lowerSpinRestriction g.val t hp hq w) := by
      intro w
      have h2 : (2 : F)=0 := by
        have hu := hneg SplitOctonion.unit
        rw [middleOctRestriction_unit g.val t hp hq] at hu
        have hh := congrFun hu 3
        simp [SplitOctonion.unit,SplitOctonion.conjugate,SplitOctonion.trace] at hh
        linear_combination hh
      have h := pairSpin_intertwining g.val t hp hq (SplitOctonion.basisVector 3) w
      rw [hneg] at h
      have hm : -SplitOctonion.conjugate (SplitOctonion.basisVector 3 : SplitOctonion.Carrier F)=
          SplitOctonion.basisVector 4 := by
        have hneg1 : (-1 : F)=1 := by linear_combination -h2
        ext j; fin_cases j <;>
          simp [SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
            SplitOctonion.basisVector,Pi.single_apply,hneg1,Matrix.vecHead,Matrix.vecTail]
      rw [hm] at h
      have hz : (![0,0,0,0,0,0] : Fin 6 → F)=0 := by
        ext i; fin_cases i <;> rfl
      simpa [middleLowerAction,SplitOctonion.basisVector,Pi.single_apply,hz] using h
    exact lowerSpinOperator_no_diagonal_swap
      (lowerSpinRestriction g.val t hp hq).toLinearMap
      (lowerSpinRestriction g.val t hp hq).injective
      (pairKernel_lower_commutes g t hp hq hker) hswap

end Atlas.F4

import Atlas.LinearGroups.F4.PairQuotientKernel

/-! The lower-spin scalar determines the opposite-line character, with the
orientation checked on actual Albert basis vectors. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

set_option maxHeartbeats 800000 in
theorem lowerSpin_cross_basis :
    cross (lowerSpinEmbed (Pi.single 0 1 : LowerSpinSpace F))
      (lowerSpinEmbed (Pi.single 7 1))= -pairOppositeVector := by
  apply Prod.ext
  · ext i; fin_cases i <;>
      simp [cross,adjoint,lowerSpinEmbed,pairOppositeVector,SplitOctonion.norm,Pi.single_apply,Matrix.vecHead,Matrix.vecTail]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [cross,adjoint,lowerSpinEmbed,pairOppositeVector,SplitOctonion.mul,
        SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,Pi.single_apply,Matrix.vecHead,Matrix.vecTail]

theorem lowerSpin_scalar_opposite_scale (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector)
    (c : F) (hc : ∀v,lowerSpinRestriction g t hp hq v=c • v) :
    (t⁻¹).val=c^2 := by
  have he (v : LowerSpinSpace F) : g.val (lowerSpinEmbed v)=c • lowerSpinEmbed v := by
    rw [←lowerSpinRestrictionMap_embed g t hp hq]
    change lowerSpinEmbed (lowerSpinRestriction g t hp hq v)=_
    rw [hc]
    exact (lowerSpinEmbedding (F:=F)).map_smul c v
  have h := stabilizer_cross g (lowerSpinEmbed (Pi.single 0 1))
    (lowerSpinEmbed (Pi.single 7 1))
  rw [he,he,cross_smul_left,cross_smul_right,lowerSpin_cross_basis,map_neg,hq] at h
  have hh := congrArg (fun x : Carrier F=>x.2 2 7) h
  simpa [pairOppositeVector,pow_two] using hh.symm

theorem pairKernel_scalar_and_scale (g : parabolicPointStabilizer (F:=F)) (t : Fˣ)
    (hp : g.val.val parabolicVector=t.val • parabolicVector)
    (hq : g.val.val pairOppositeVector=(t⁻¹).val • pairOppositeVector)
    (hker : parabolicOrthogonalHom g=1) :
    ∃ c : F, c≠0 ∧ (t⁻¹).val=c^2 ∧
      ∀v, lowerSpinRestriction g.val t hp hq v=c • v := by
  obtain ⟨c,hc,hact⟩ := pairKernel_lower_scalar g t hp hq hker
  exact ⟨c,hc,lowerSpin_scalar_opposite_scale g.val t hp hq c hact,hact⟩

end Atlas.F4

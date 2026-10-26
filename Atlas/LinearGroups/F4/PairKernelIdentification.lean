import Atlas.LinearGroups.F4.PairKernelScale
import Atlas.LinearGroups.F4.ScalarTorusActions

/-! Reconstruction of the full actual opposite-pair quotient kernel from its
lower-spin scalar. The scalar is realized by the existing diagonal torus. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def upperSpinCoordinates (x : Carrier F) : LowerSpinSpace F :=
  ![x.2 0 0,x.2 0 1,x.2 0 2,x.2 0 3,x.2 1 0,x.2 1 1,x.2 1 2,x.2 1 4]

def upperSpinCrossPreimage (v : LowerSpinSpace F) : LowerSpinSpace F :=
  ![-v 4,-v 5,v 6,-v 7,-v 0,v 1,-v 2,-v 3]

theorem upperSpin_as_cross (v : LowerSpinSpace F) :
    upperSpinEmbed v=cross parabolicVector (lowerSpinEmbed (upperSpinCrossPreimage v)) := by
  change upperSpinEmbed v=parabolicCross (lowerSpinEmbed (upperSpinCrossPreimage v))
  rw [parabolicCross_coordinates]
  apply Prod.ext
  · ext i; fin_cases i <;> simp [upperSpinEmbed,lowerSpinEmbed]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [upperSpinEmbed,lowerSpinEmbed,upperSpinCrossPreimage]

theorem pairSpin_decomposition (x : Carrier F) :
    x=lowerSpinEmbed (lowerSpinCoordinates x)+upperSpinEmbed (upperSpinCoordinates x)+
      middleOctEmbed (middleOctCoordinates x)+x.1 2 • pairDiagonalVector+
      x.2 2 0 • parabolicVector+x.2 2 7 • pairOppositeVector := by
  apply Prod.ext
  · ext i; fin_cases i <;>
      simp [lowerSpinEmbed,upperSpinEmbed,middleOctEmbed,middleSpinEmbed,middleOctCoordinates,
        pairDiagonalVector,parabolicVector,pairOppositeVector]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [lowerSpinEmbed,lowerSpinCoordinates,upperSpinEmbed,upperSpinCoordinates,
        middleOctEmbed,middleSpinEmbed,middleOctCoordinates,pairDiagonalVector,
        parabolicVector,pairOppositeVector]

theorem model_eq_of_pairSpin (g h : Model F)
    (hp : g.val parabolicVector=h.val parabolicVector)
    (hq : g.val pairOppositeVector=h.val pairOppositeVector)
    (hd : g.val pairDiagonalVector=h.val pairDiagonalVector)
    (hl : ∀v,g.val (lowerSpinEmbed v)=h.val (lowerSpinEmbed v))
    (hm : ∀v,g.val (middleOctEmbed v)=h.val (middleOctEmbed v)) : g=h := by
  have hu (v : LowerSpinSpace F) : g.val (upperSpinEmbed v)=h.val (upperSpinEmbed v) := by
    rw [upperSpin_as_cross,←stabilizer_cross,←stabilizer_cross,hp,hl]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  conv_lhs => rw [pairSpin_decomposition x]
  conv_rhs => rw [pairSpin_decomposition x]
  simp only [_root_.map_add,map_smul,hl,hu,hm,hd,hp,hq]

theorem pairKernel_eq_scalarTorus (g : parabolicPointStabilizer (F:=F)) (t : Fˣ)
    (hp : g.val.val parabolicVector=t.val • parabolicVector)
    (hq : g.val.val pairOppositeVector=(t⁻¹).val • pairOppositeVector)
    (hker : parabolicOrthogonalHom g=1) : ∃ a : Fˣ, g.val=scalarTorus a := by
  obtain ⟨c,hc,hscale,hact⟩ := pairKernel_scalar_and_scale g t hp hq hker
  let u : Fˣ := Units.mk0 c hc
  have hu : (u:F)=c := rfl
  have htinv : t⁻¹=u^2 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val,hu] using hscale
  have ht : t=u⁻¹^2 := by
    calc t=(t⁻¹)⁻¹ := (inv_inv t).symm
         _=(u^2)⁻¹ := congrArg Inv.inv htinv
         _=u⁻¹^2 := inv_pow u 2
  refine ⟨u⁻¹,model_eq_of_pairSpin g.val (scalarTorus u⁻¹) ?_ ?_ ?_ ?_ ?_⟩
  · rw [hp,scalarTorus_C0,ht]
    simp
  · rw [hq,scalarTorus_C7,htinv]
    simp
  · rw [pairStabilizer_fixes_diagonal g.val t hp hq,scalarTorus_apply]
    apply Prod.ext
    · rfl
    · ext i j; fin_cases i <;> fin_cases j <;> simp [scalarTorusApply,pairDiagonalVector]
  · intro v
    rw [←lowerSpinRestrictionMap_embed g.val t hp hq,scalarTorus_match_lower]
    change lowerSpinEmbed (lowerSpinRestriction g.val t hp hq v)=_
    rw [hact,hu]
    exact (lowerSpinEmbedding (F:=F)).map_smul c v
  · intro v
    rw [←middleOctRestrictionMap_embed g.val t hp hq,scalarTorus_middleOct]
    change middleOctEmbed (middleOctRestriction g.val t hp hq v)=_
    rw [pairKernel_middle_identity g t hp hq hker]

end Atlas.F4

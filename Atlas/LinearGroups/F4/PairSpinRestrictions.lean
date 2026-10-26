import Atlas.LinearGroups.F4.LowerSpinOperators
import Atlas.LinearGroups.F4.PairCrossProjections
import Atlas.LinearGroups.F4.OppositeCellParabolicAction

/-! Intrinsic restrictions of an actual opposite-pair stabilizer to its two
middle and lower eight-dimensional spaces. No Levi image theorem is assumed. -/
set_option maxHeartbeats 600000
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def lowerSpinCoordinates (x : Carrier F) : LowerSpinSpace F :=
  ![x.2 0 4,x.2 0 5,x.2 0 6,x.2 0 7,x.2 1 3,x.2 1 5,x.2 1 6,x.2 1 7]

def middleOctEmbed (v : SplitOctonion.Carrier F) : Carrier F :=
  middleSpinEmbed (v 3) (v 4) ![v 0,v 1,v 2,-v 5,-v 6,-v 7]

def middleOctCoordinates (x : Carrier F) : SplitOctonion.Carrier F :=
  ![x.2 2 1,x.2 2 2,x.2 2 3,x.1 0,x.1 1,-x.2 2 4,-x.2 2 5,-x.2 2 6]

def lowerSpinEmbedding : LowerSpinSpace F →ₗ[F] Carrier F where
  toFun := lowerSpinEmbed
  map_add' v w := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [lowerSpinEmbed]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [lowerSpinEmbed]
  map_smul' t v := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [lowerSpinEmbed]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [lowerSpinEmbed]

def lowerSpinExtraction : Carrier F →ₗ[F] LowerSpinSpace F where
  toFun := lowerSpinCoordinates
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' t v := by ext i; fin_cases i <;> rfl

def middleOctEmbedding : SplitOctonion.Carrier F →ₗ[F] Carrier F where
  toFun := middleOctEmbed
  map_add' v w := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [middleOctEmbed,middleSpinEmbed]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [middleOctEmbed,middleSpinEmbed] <;> ring
  map_smul' t v := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [middleOctEmbed,middleSpinEmbed]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [middleOctEmbed,middleSpinEmbed]

def middleOctExtraction : Carrier F →ₗ[F] SplitOctonion.Carrier F where
  toFun := middleOctCoordinates
  map_add' v w := by ext i; fin_cases i <;> simp [middleOctCoordinates,Matrix.vecHead,Matrix.vecTail] <;> ring
  map_smul' t v := by ext i; fin_cases i <;> simp [middleOctCoordinates,Matrix.vecHead,Matrix.vecTail]

@[simp] theorem lowerSpin_extract_embed (v : LowerSpinSpace F) :
    lowerSpinCoordinates (lowerSpinEmbed v)=v := by ext i; fin_cases i <;> rfl
@[simp] theorem middleOct_extract_embed (v : SplitOctonion.Carrier F) :
    middleOctCoordinates (middleOctEmbed v)=v := by
  ext i; fin_cases i <;> simp [middleOctCoordinates,middleOctEmbed,middleSpinEmbed]

theorem lowerSpinEmbed_injective : Function.Injective (lowerSpinEmbed (F:=F)) :=
  Function.LeftInverse.injective lowerSpin_extract_embed
theorem middleOctEmbed_injective : Function.Injective (middleOctEmbed (F:=F)) :=
  Function.LeftInverse.injective middleOct_extract_embed

theorem lowerSpin_reconstruction (x : Carrier F) :
    lowerSpinEmbed (lowerSpinCoordinates x)=pairLowerProjection x-pairDiagonalProjection x-
      x.2 2 7 • pairOppositeVector := by
  rw [pairLowerProjection_coordinates,pairDiagonalProjection_coordinates]
  apply Prod.ext
  · ext i; fin_cases i <;> simp [lowerSpinEmbed,pairOppositeVector]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [lowerSpinEmbed,lowerSpinCoordinates,pairOppositeVector]

theorem middleOct_reconstruction (x : Carrier F) :
    middleOctEmbed (middleOctCoordinates x)=x-pairUpperProjection x-
      pairLowerProjection x+pairDiagonalProjection x := by
  rw [pairUpperProjection_coordinates,pairLowerProjection_coordinates,pairDiagonalProjection_coordinates]
  apply Prod.ext
  · ext i; fin_cases i <;> simp [middleOctEmbed,middleSpinEmbed,middleOctCoordinates,Matrix.vecHead,Matrix.vecTail]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [middleOctEmbed,middleSpinEmbed,middleOctCoordinates,Matrix.vecHead,Matrix.vecTail]

theorem pairInverse_scales (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector) :
    (g⁻¹).val parabolicVector=(t⁻¹).val • parabolicVector ∧
      (g⁻¹).val pairOppositeVector=t.val • pairOppositeVector := by
  constructor
  · apply g.val.injective
    change g.val (g.val.symm parabolicVector)=g.val ((t⁻¹).val • parabolicVector)
    rw [LinearEquiv.apply_symm_apply,map_smul,hp,smul_smul]
    simp
  · apply g.val.injective
    change g.val (g.val.symm pairOppositeVector)=g.val (t.val • pairOppositeVector)
    rw [LinearEquiv.apply_symm_apply,map_smul,hq,smul_smul]
    simp

theorem pairDiagonalProjection_stable (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector) (x : Carrier F) :
    g.val (pairDiagonalProjection x)=pairDiagonalProjection (g.val x) := by
  change g.val (pairUpperProjection (pairLowerProjection x))=_
  rw [pairUpperProjection_stable g t hp hq,pairLowerProjection_stable g t hp hq]
  rfl

theorem lowerSpin_reconstruction_stable (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector) (x : Carrier F) :
    g.val (lowerSpinEmbed (lowerSpinCoordinates x))=
      lowerSpinEmbed (lowerSpinCoordinates (g.val x)) := by
  have hc := stabilizer_tracePairing g parabolicVector x
  rw [hp,tracePairing_smul_left,parabolicPairing_C7,parabolicPairing_C7] at hc
  rw [lowerSpin_reconstruction,lowerSpin_reconstruction,map_sub,map_sub,map_smul,
    pairLowerProjection_stable g t hp hq,pairDiagonalProjection_stable g t hp hq,hq,smul_smul]
  congr 2
  rw [←hc]
  simp [mul_assoc,mul_comm,mul_left_comm]

theorem middleOct_reconstruction_stable (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector) (x : Carrier F) :
    g.val (middleOctEmbed (middleOctCoordinates x))=
      middleOctEmbed (middleOctCoordinates (g.val x)) := by
  rw [middleOct_reconstruction,middleOct_reconstruction,_root_.map_add,map_sub,map_sub,
    pairUpperProjection_stable g t hp hq,pairLowerProjection_stable g t hp hq,
    pairDiagonalProjection_stable g t hp hq]

def lowerSpinRestrictionMap (g : Model F) : LowerSpinSpace F →ₗ[F] LowerSpinSpace F :=
  lowerSpinExtraction.comp (g.val.toLinearMap.comp lowerSpinEmbedding)
def middleOctRestrictionMap (g : Model F) : SplitOctonion.Carrier F →ₗ[F] SplitOctonion.Carrier F :=
  middleOctExtraction.comp (g.val.toLinearMap.comp middleOctEmbedding)

theorem lowerSpinRestrictionMap_embed (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector) (v : LowerSpinSpace F) :
    lowerSpinEmbed (lowerSpinRestrictionMap g v)=g.val (lowerSpinEmbed v) := by
  change lowerSpinEmbed (lowerSpinCoordinates (g.val (lowerSpinEmbed v)))=_
  simpa only [lowerSpin_extract_embed] using
    (lowerSpin_reconstruction_stable g t hp hq (lowerSpinEmbed v)).symm

theorem middleOctRestrictionMap_embed (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector) (v : SplitOctonion.Carrier F) :
    middleOctEmbed (middleOctRestrictionMap g v)=g.val (middleOctEmbed v) := by
  change middleOctEmbed (middleOctCoordinates (g.val (middleOctEmbed v)))=_
  simpa only [middleOct_extract_embed] using
    (middleOct_reconstruction_stable g t hp hq (middleOctEmbed v)).symm

def lowerSpinRestriction (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector) :
    LowerSpinSpace F ≃ₗ[F] LowerSpinSpace F where
  toLinearMap := lowerSpinRestrictionMap g
  invFun := lowerSpinRestrictionMap g⁻¹
  left_inv v := by
    apply lowerSpinEmbed_injective
    calc lowerSpinEmbed (lowerSpinRestrictionMap g⁻¹ (lowerSpinRestrictionMap g v)) =
        (g⁻¹).val (lowerSpinEmbed (lowerSpinRestrictionMap g v)) :=
          lowerSpinRestrictionMap_embed g⁻¹ t⁻¹ (pairInverse_scales g t hp hq).1
            (by simpa using (pairInverse_scales g t hp hq).2) _
      _=(g⁻¹).val (g.val (lowerSpinEmbed v)) :=
        congrArg (g⁻¹).val (lowerSpinRestrictionMap_embed g t hp hq v)
      _=lowerSpinEmbed v := g.val.symm_apply_apply _
  right_inv v := by
    apply lowerSpinEmbed_injective
    calc lowerSpinEmbed (lowerSpinRestrictionMap g (lowerSpinRestrictionMap g⁻¹ v)) =
        g.val (lowerSpinEmbed (lowerSpinRestrictionMap g⁻¹ v)) :=
          lowerSpinRestrictionMap_embed g t hp hq _
      _=g.val ((g⁻¹).val (lowerSpinEmbed v)) :=
        congrArg g.val (lowerSpinRestrictionMap_embed g⁻¹ t⁻¹
          (pairInverse_scales g t hp hq).1 (by simpa using (pairInverse_scales g t hp hq).2) v)
      _=lowerSpinEmbed v := g.val.apply_symm_apply _

def middleOctRestriction (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector) :
    SplitOctonion.Carrier F ≃ₗ[F] SplitOctonion.Carrier F where
  toLinearMap := middleOctRestrictionMap g
  invFun := middleOctRestrictionMap g⁻¹
  left_inv v := by
    apply middleOctEmbed_injective
    calc middleOctEmbed (middleOctRestrictionMap g⁻¹ (middleOctRestrictionMap g v)) =
        (g⁻¹).val (middleOctEmbed (middleOctRestrictionMap g v)) :=
          middleOctRestrictionMap_embed g⁻¹ t⁻¹ (pairInverse_scales g t hp hq).1
            (by simpa using (pairInverse_scales g t hp hq).2) _
      _=(g⁻¹).val (g.val (middleOctEmbed v)) :=
        congrArg (g⁻¹).val (middleOctRestrictionMap_embed g t hp hq v)
      _=middleOctEmbed v := g.val.symm_apply_apply _
  right_inv v := by
    apply middleOctEmbed_injective
    calc middleOctEmbed (middleOctRestrictionMap g (middleOctRestrictionMap g⁻¹ v)) =
        g.val (middleOctEmbed (middleOctRestrictionMap g⁻¹ v)) :=
          middleOctRestrictionMap_embed g t hp hq _
      _=g.val ((g⁻¹).val (middleOctEmbed v)) :=
        congrArg g.val (middleOctRestrictionMap_embed g⁻¹ t⁻¹
          (pairInverse_scales g t hp hq).1 (by simpa using (pairInverse_scales g t hp hq).2) v)
      _=middleOctEmbed v := g.val.apply_symm_apply _

theorem middleOctEmbed_unit : middleOctEmbed (SplitOctonion.unit : SplitOctonion.Carrier F)=
    unit-pairDiagonalVector := by
  apply Prod.ext
  · ext i; fin_cases i <;> simp [middleOctEmbed,middleSpinEmbed,SplitOctonion.unit,unit,pairDiagonalVector,Matrix.vecHead,Matrix.vecTail]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [middleOctEmbed,middleSpinEmbed,SplitOctonion.unit,unit,pairDiagonalVector,Matrix.vecHead,Matrix.vecTail]

theorem middleOctRestriction_unit (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector) :
    middleOctRestriction g t hp hq SplitOctonion.unit=SplitOctonion.unit := by
  apply middleOctEmbed_injective
  change middleOctEmbed (middleOctRestrictionMap g SplitOctonion.unit)=_
  rw [middleOctRestrictionMap_embed g t hp hq,middleOctEmbed_unit,map_sub,
    stabilizer_unit,pairStabilizer_fixes_diagonal g t hp hq]

theorem middleOctEmbed_quadraticTrace (v : SplitOctonion.Carrier F) :
    quadraticTrace (middleOctEmbed v)=SplitOctonion.norm v := by
  simp [quadraticTrace,middleOctEmbed,middleSpinEmbed,SplitOctonion.norm]
  ring

theorem middleOctRestriction_norm (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector) (v : SplitOctonion.Carrier F) :
    SplitOctonion.norm (middleOctRestriction g t hp hq v)=SplitOctonion.norm v := by
  rw [←middleOctEmbed_quadraticTrace,←middleOctEmbed_quadraticTrace v]
  change quadraticTrace (middleOctEmbed (middleOctRestrictionMap g v))=_
  rw [middleOctRestrictionMap_embed g t hp hq,stabilizer_quadraticTrace]

def middleLowerAction (m : SplitOctonion.Carrier F) (v : LowerSpinSpace F) : LowerSpinSpace F :=
  lowerSpinAction (m 3) (m 4) ![m 0,m 1,m 2,-m 5,-m 6,-m 7] v

theorem middleOct_cross_lowerSpin (m : SplitOctonion.Carrier F) (v : LowerSpinSpace F) :
    cross (middleOctEmbed m) (lowerSpinEmbed v)=lowerSpinEmbed (middleLowerAction m v) :=
  middle_cross_lowerSpin _ _ _ _

theorem pairSpin_intertwining (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector)
    (m : SplitOctonion.Carrier F) (v : LowerSpinSpace F) :
    lowerSpinRestriction g t hp hq (middleLowerAction m v)=
      middleLowerAction (middleOctRestriction g t hp hq m) (lowerSpinRestriction g t hp hq v) := by
  apply lowerSpinEmbed_injective
  change lowerSpinEmbed (lowerSpinRestrictionMap g (middleLowerAction m v))=
    lowerSpinEmbed (middleLowerAction (middleOctRestrictionMap g m) (lowerSpinRestrictionMap g v))
  rw [lowerSpinRestrictionMap_embed g t hp hq,←middleOct_cross_lowerSpin,←stabilizer_cross,
    ←middleOctRestrictionMap_embed g t hp hq,←lowerSpinRestrictionMap_embed g t hp hq,
    middleOct_cross_lowerSpin]

end Atlas.F4


import Atlas.LinearGroups.F4.PairSpinRestrictions
import Atlas.LinearGroups.F4.TorusNorm

/-! The actual scalar torus in the Levi kernel: no square root is required
when matching a scalar on the lower spin space. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def scalarTorusParameters (a : Fˣ) : TorusParameters F := ![1,1,1,a]
def scalarTorus (a : Fˣ) : Model F := diagonalTorus (scalarTorusParameters a)

def scalarTorusApply (a : Fˣ) (x : Carrier F) : Carrier F :=
  (x.1,
    ![![(a:F)*x.2 0 0,(a:F)*x.2 0 1,(a:F)*x.2 0 2,(a:F)*x.2 0 3,
        ((a⁻¹:Fˣ):F)*x.2 0 4,((a⁻¹:Fˣ):F)*x.2 0 5,
        ((a⁻¹:Fˣ):F)*x.2 0 6,((a⁻¹:Fˣ):F)*x.2 0 7],
      ![(a:F)*x.2 1 0,(a:F)*x.2 1 1,(a:F)*x.2 1 2,((a⁻¹:Fˣ):F)*x.2 1 3,
        (a:F)*x.2 1 4,((a⁻¹:Fˣ):F)*x.2 1 5,((a⁻¹:Fˣ):F)*x.2 1 6,((a⁻¹:Fˣ):F)*x.2 1 7],
      ![(a:F)^2*x.2 2 0,x.2 2 1,x.2 2 2,x.2 2 3,x.2 2 4,x.2 2 5,x.2 2 6,
        ((a⁻¹:Fˣ):F)^2*x.2 2 7]])

set_option maxHeartbeats 1000000 in
theorem scalarTorus_apply (a : Fˣ) (x : Carrier F) :
    (scalarTorus a).val x=scalarTorusApply a x := by
  change torusApply (scalarTorusParameters a) x=_
  apply Prod.ext
  · rfl
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [torusApply,torusScale,weightCharacter,scalarTorusParameters,scalarTorusApply,
        RootData.simpleCoefficients,RootData.coordinates,Weights.slotRoot,
        Fin.prod_univ_succ,pow_two]

theorem scalarTorus_injective : Function.Injective (scalarTorus (F:=F)) := by
  intro a b h
  have hh := diagonalTorus_injective h
  exact congrFun hh 3

theorem scalarTorus_mul (a b : Fˣ) : scalarTorus (a*b)=scalarTorus a*scalarTorus b := by
  have h : scalarTorusParameters (a*b)=scalarTorusParameters a*scalarTorusParameters b := by
    ext i
    fin_cases i <;> simp [scalarTorusParameters]
  exact (congrArg diagonalTorus h).trans (map_mul diagonalTorus _ _)

theorem scalarTorus_lowerSpin (a : Fˣ) (v : LowerSpinSpace F) :
    (scalarTorus a).val (lowerSpinEmbed v)=((a⁻¹:Fˣ):F) • lowerSpinEmbed v := by
  rw [scalarTorus_apply]
  apply Prod.ext
  · ext i; fin_cases i <;> simp [scalarTorusApply,lowerSpinEmbed]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [scalarTorusApply,lowerSpinEmbed]

/-- The complementary upper eight-space in the fixed Albert coordinates. -/
def upperSpinEmbed (v : LowerSpinSpace F) : Carrier F :=
  (0,![![v 0,v 1,v 2,v 3,0,0,0,0],![v 4,v 5,v 6,0,v 7,0,0,0],0])

theorem scalarTorus_upperSpin (a : Fˣ) (v : LowerSpinSpace F) :
    (scalarTorus a).val (upperSpinEmbed v)=(a:F) • upperSpinEmbed v := by
  rw [scalarTorus_apply]
  apply Prod.ext
  · ext i; fin_cases i <;> simp [scalarTorusApply,upperSpinEmbed]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [scalarTorusApply,upperSpinEmbed]

theorem scalarTorus_middleOct (a : Fˣ) (v : SplitOctonion.Carrier F) :
    (scalarTorus a).val (middleOctEmbed v)=middleOctEmbed v := by
  rw [scalarTorus_apply]
  apply Prod.ext
  · rfl
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [scalarTorusApply,middleOctEmbed,middleSpinEmbed]

theorem scalarTorus_C0 (a : Fˣ) :
    (scalarTorus a).val parabolicVector=(a:F)^2 • parabolicVector := by
  rw [scalarTorus_apply]
  apply Prod.ext
  · ext i; fin_cases i <;> simp [scalarTorusApply,parabolicVector]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [scalarTorusApply,parabolicVector]

theorem scalarTorus_C7 (a : Fˣ) :
    (scalarTorus a).val pairOppositeVector=((a⁻¹:Fˣ):F)^2 • pairOppositeVector := by
  rw [scalarTorus_apply]
  apply Prod.ext
  · ext i; fin_cases i <;> simp [scalarTorusApply,pairOppositeVector]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [scalarTorusApply,pairOppositeVector]

/-- Any prescribed nonzero lower scalar is attained directly. -/
theorem scalarTorus_match_lower (c : Fˣ) (v : LowerSpinSpace F) :
    (scalarTorus c⁻¹).val (lowerSpinEmbed v)=(c:F) • lowerSpinEmbed v := by
  simpa using scalarTorus_lowerSpin c⁻¹ v

end Atlas.F4

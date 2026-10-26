import Atlas.LinearGroups.F4.OppositeCrossMarked
import Atlas.LinearGroups.F4.PointFiltrationCovariance

/-! Intrinsic commuting projections associated with the two opposite marked lines.
The identities are valid also in characteristics two and three. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def pairUpperProjection : Carrier F →ₗ[F] Carrier F := parabolicCross.comp pairOppositeCross
def pairLowerProjection : Carrier F →ₗ[F] Carrier F := pairOppositeCross.comp parabolicCross

theorem pairUpperProjection_coordinates (x : Carrier F) :
    pairUpperProjection x=(![0,0,x.1 2],
      ![![x.2 0 0,x.2 0 1,x.2 0 2,x.2 0 3,0,0,0,0],
        ![x.2 1 0,x.2 1 1,x.2 1 2,0,x.2 1 4,0,0,0],
        ![x.2 2 0,0,0,0,0,0,0,0]]) := by
  change parabolicCross (pairOppositeCross x)=_
  rw [pairOppositeCross_coordinates,parabolicCross_coordinates]
  apply Prod.ext
  · ext i; fin_cases i <;> simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp

theorem pairLowerProjection_coordinates (x : Carrier F) :
    pairLowerProjection x=(![0,0,x.1 2],
      ![![0,0,0,0,x.2 0 4,x.2 0 5,x.2 0 6,x.2 0 7],
        ![0,0,0,x.2 1 3,0,x.2 1 5,x.2 1 6,x.2 1 7],
        ![0,0,0,0,0,0,0,x.2 2 7]]) := by
  change pairOppositeCross (parabolicCross x)=_
  rw [parabolicCross_coordinates,pairOppositeCross_coordinates]
  apply Prod.ext
  · ext i; fin_cases i <;> simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp

def pairDiagonalProjection : Carrier F →ₗ[F] Carrier F :=
  pairUpperProjection.comp pairLowerProjection

theorem pairDiagonalProjection_coordinates (x : Carrier F) :
    pairDiagonalProjection x=(![0,0,x.1 2],0) := by
  change pairUpperProjection (pairLowerProjection x)=_
  rw [pairLowerProjection_coordinates,pairUpperProjection_coordinates]
  apply Prod.ext
  · ext i; fin_cases i <;> rfl
  · ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem pairUpperProjection_idempotent (x : Carrier F) :
    pairUpperProjection (pairUpperProjection x)=pairUpperProjection x := by
  simp only [pairUpperProjection_coordinates]
  rfl

theorem pairLowerProjection_idempotent (x : Carrier F) :
    pairLowerProjection (pairLowerProjection x)=pairLowerProjection x := by
  simp only [pairLowerProjection_coordinates]
  rfl

theorem pairProjections_commute (x : Carrier F) :
    pairLowerProjection (pairUpperProjection x)=pairDiagonalProjection x := by
  rw [pairUpperProjection_coordinates,pairLowerProjection_coordinates,pairDiagonalProjection_coordinates]
  apply Prod.ext
  · ext i; fin_cases i <;> rfl
  · ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem pairOppositeCross_covariant (g : Model F) (t : Fˣ)
    (hg : g.val pairOppositeVector=t.val • pairOppositeVector) (x : Carrier F) :
    g.val (pairOppositeCross x)=t.val • pairOppositeCross (g.val x) := by
  change g.val (cross pairOppositeVector x)=t.val • cross pairOppositeVector (g.val x)
  rw [←stabilizer_cross,hg,cross_smul_left]

theorem pairUpperProjection_stable (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector) (x : Carrier F) :
    g.val (pairUpperProjection x)=pairUpperProjection (g.val x) := by
  change g.val (parabolicCross (pairOppositeCross x))=_
  rw [parabolicCross_covariant g t hp,pairOppositeCross_covariant g t⁻¹ hq,map_smul,smul_smul]
  simp [pairUpperProjection]

theorem pairLowerProjection_stable (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector) (x : Carrier F) :
    g.val (pairLowerProjection x)=pairLowerProjection (g.val x) := by
  change g.val (pairOppositeCross (parabolicCross x))=_
  rw [pairOppositeCross_covariant g t⁻¹ hq,parabolicCross_covariant g t hp,map_smul,smul_smul]
  simp [pairLowerProjection]

def pairDiagonalVector : Carrier F := (![0,0,1],0)

theorem pairUpperProjection_unit : pairUpperProjection (unit : Carrier F)=pairDiagonalVector := by
  rw [pairUpperProjection_coordinates]
  apply Prod.ext
  · ext i; fin_cases i <;> rfl
  · ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem pairStabilizer_fixes_diagonal (g : Model F) (t : Fˣ)
    (hp : g.val parabolicVector=t.val • parabolicVector)
    (hq : g.val pairOppositeVector=(t⁻¹).val • pairOppositeVector) :
    g.val pairDiagonalVector=pairDiagonalVector := by
  have h := pairUpperProjection_stable g t hp hq unit
  rwa [pairUpperProjection_unit,stabilizer_unit,pairUpperProjection_unit] at h

end Atlas.F4

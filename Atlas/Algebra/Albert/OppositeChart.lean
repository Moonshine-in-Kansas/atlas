import Atlas.Algebra.Albert.OppositeChartFormula
import Mathlib.Tactic.LinearCombination
import Mathlib.SetTheory.Cardinal.Finite

/-! Exact reconstruction and the fifteen-dimensional opposite affine cell. -/
noncomputable section
namespace Atlas.Albert
variable {F : Type*} [Field F]

def oppositeU (x : Carrier F) : Fin 4→F := ![x.2 0 4,x.2 0 5,x.2 0 6,x.2 0 7]
def oppositeV (x : Carrier F) : Fin 4→F := ![x.2 1 3,x.2 1 5,x.2 1 6,x.2 1 7]
def oppositeZ (x : Carrier F) : Fin 6→F := ![x.2 2 1,x.2 2 2,x.2 2 3,x.2 2 4,x.2 2 5,x.2 2 6]

theorem eq_oppositeChart (x : Carrier F) (hx : adjoint x=0) (h7 : x.2 2 7=1) :
    x=oppositeChart (x.1 0) (x.1 1) (oppositeU x) (oppositeV x) (oppositeZ x) := by
  apply Prod.ext
  · ext i
    fin_cases i
    · rfl
    · rfl
    · have h := congrArg (fun y : Carrier F=>y.2 2 7) hx
      simp [adjoint,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
        SplitOctonion.unit,h7,Matrix.vecHead,Matrix.vecTail] at h
      dsimp [oppositeChart,oppositeDiagonalC,oppositeU,oppositeV]
      linear_combination -h
  · ext i j
    fin_cases i
    · fin_cases j
      · have h := congrArg (fun y : Carrier F=>y.2 1 3) hx
        simp [adjoint,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
          SplitOctonion.unit,h7,Matrix.vecHead,Matrix.vecTail] at h
        dsimp [oppositeChart,oppositeA,oppositeB,oppositeU,oppositeV,oppositeZ]
        linear_combination -h
      · have h := congrArg (fun y : Carrier F=>y.2 1 5) hx
        simp [adjoint,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
          SplitOctonion.unit,h7,Matrix.vecHead,Matrix.vecTail] at h
        dsimp [oppositeChart,oppositeA,oppositeB,oppositeU,oppositeV,oppositeZ]
        linear_combination h
      · have h := congrArg (fun y : Carrier F=>y.2 1 6) hx
        simp [adjoint,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
          SplitOctonion.unit,h7,Matrix.vecHead,Matrix.vecTail] at h
        dsimp [oppositeChart,oppositeA,oppositeB,oppositeU,oppositeV,oppositeZ]
        linear_combination -h
      · have h := congrArg (fun y : Carrier F=>y.2 1 7) hx
        simp [adjoint,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
          SplitOctonion.unit,h7,Matrix.vecHead,Matrix.vecTail] at h
        dsimp [oppositeChart,oppositeA,oppositeB,oppositeU,oppositeV,oppositeZ]
        linear_combination -h
      · rfl
      · rfl
      · rfl
      · rfl
    · fin_cases j
      · have h := congrArg (fun y : Carrier F=>y.2 0 4) hx
        simp [adjoint,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
          SplitOctonion.unit,h7,Matrix.vecHead,Matrix.vecTail] at h
        dsimp [oppositeChart,oppositeA,oppositeB,oppositeU,oppositeV,oppositeZ]
        linear_combination -h
      · have h := congrArg (fun y : Carrier F=>y.2 0 5) hx
        simp [adjoint,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
          SplitOctonion.unit,h7,Matrix.vecHead,Matrix.vecTail] at h
        dsimp [oppositeChart,oppositeA,oppositeB,oppositeU,oppositeV,oppositeZ]
        linear_combination -h
      · have h := congrArg (fun y : Carrier F=>y.2 0 6) hx
        simp [adjoint,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
          SplitOctonion.unit,h7,Matrix.vecHead,Matrix.vecTail] at h
        dsimp [oppositeChart,oppositeA,oppositeB,oppositeU,oppositeV,oppositeZ]
        linear_combination h
      · rfl
      · have h := congrArg (fun y : Carrier F=>y.2 0 7) hx
        simp [adjoint,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
          SplitOctonion.unit,h7,Matrix.vecHead,Matrix.vecTail] at h
        dsimp [oppositeChart,oppositeA,oppositeB,oppositeU,oppositeV,oppositeZ]
        linear_combination -h
      · rfl
      · rfl
      · rfl
    · fin_cases j
      · have h := congrArg (fun y : Carrier F=>y.1 2) hx
        simp [adjoint,SplitOctonion.norm,h7,Matrix.vecHead,Matrix.vecTail] at h
        change x.2 2 0 = x.1 0*x.1 1-x.2 2 1*x.2 2 6-x.2 2 2*x.2 2 5-x.2 2 3*x.2 2 4
        linear_combination -h
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact h7

theorem eq_oppositeZeroChart (x : Carrier F) (hx : adjoint x=0)
    (ht : trace x=0) (h7 : x.2 2 7=1) :
    x=oppositeZeroChart (x.1 0) (oppositeU x) (oppositeV x) (oppositeZ x) := by
  have he := eq_oppositeChart x hx h7
  have hc : x.1 2=oppositeDiagonalC (oppositeU x) (oppositeV x) :=
    congrArg (fun y : Carrier F=>y.1 2) he
  have hb : x.1 1 = -x.1 0-oppositeDiagonalC (oppositeU x) (oppositeV x) := by
    change x.1 0+x.1 1+x.1 2=0 at ht
    rw [hc] at ht
    linear_combination ht
  simpa only [hb,oppositeZeroChart] using he

abbrev OppositeParameters (F : Type*) := F × (Fin 4→F) × (Fin 4→F) × (Fin 6→F)
abbrev OppositeCell (F : Type*) [Field F] :=
  {x : Carrier F // adjoint x=0 ∧ trace x=0 ∧ x.2 2 7=1}

def oppositeCellEquiv : OppositeParameters F ≃ OppositeCell F where
  toFun v := ⟨oppositeZeroChart v.1 v.2.1 v.2.2.1 v.2.2.2,
    oppositeZeroChart_adjoint _ _ _ _,oppositeZeroChart_trace _ _ _ _,
    oppositeZeroChart_C7 _ _ _ _⟩
  invFun x := (x.val.1 0,oppositeU x.val,oppositeV x.val,oppositeZ x.val)
  left_inv v := by
    rcases v with ⟨a,u,v,z⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · ext i; fin_cases i <;> rfl
      · apply Prod.ext
        · ext i; fin_cases i <;> rfl
        · ext i; fin_cases i <;> rfl
  right_inv x := by
    apply Subtype.ext
    exact (eq_oppositeZeroChart x.val x.prop.1 x.prop.2.1 x.prop.2.2).symm

theorem oppositeCell_card [Finite F] : Nat.card (OppositeCell F)=Nat.card F^15 := by
  rw [←Nat.card_congr (oppositeCellEquiv (F:=F))]
  simp only [OppositeParameters,Nat.card_prod,Nat.card_fun,Nat.card_fin]
  ring

end Atlas.Albert

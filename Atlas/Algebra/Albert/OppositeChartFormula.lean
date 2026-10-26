import Atlas.Algebra.Albert.Adjoint

/-! Polynomial coordinates on the C₇=1 open chart of the rank-one Albert cone.
All formulas are integral: no division or characteristic restriction occurs. -/
namespace Atlas.Albert
variable {F : Type*} [CommRing F]

def oppositeDiagonalC (u v : Fin 4→F) : F :=
  -u 0*v 3-u 1*v 2+u 2*v 1-u 3*v 0

def oppositeC (a b : F) (z : Fin 6→F) : SplitOctonion.Carrier F :=
  ![a*b-z 0*z 5-z 1*z 4-z 2*z 3,z 0,z 1,z 2,z 3,z 4,z 5,1]

def oppositeA (b : F) (u v : Fin 4→F) (z : Fin 6→F) : SplitOctonion.Carrier F :=
  ![-z 0*u 2-z 1*u 1+z 3*u 0-b*v 0,
    z 0*u 3+z 2*u 1+z 4*u 0+b*v 1,
    z 1*u 3-z 2*u 2-z 5*u 0-b*v 2,
    -z 3*u 3-z 4*u 2+z 5*u 1-b*v 3,
    u 0,u 1,u 2,u 3]

def oppositeB (a : F) (u v : Fin 4→F) (z : Fin 6→F) : SplitOctonion.Carrier F :=
  ![v 0*z 2-v 1*z 1-v 2*z 0-a*u 0,
    -v 0*z 4-v 1*z 3+v 3*z 0-a*u 1,
    v 0*z 5+v 2*z 3+v 3*z 1+a*u 2,
    v 0,-v 1*z 5+v 2*z 4-v 3*z 2-a*u 3,v 1,v 2,v 3]

def oppositeChart (a b : F) (u v : Fin 4→F) (z : Fin 6→F) : Carrier F :=
  (![a,b,oppositeDiagonalC u v],![oppositeA b u v z,oppositeB a u v z,oppositeC a b z])

set_option maxHeartbeats 4000000 in
-- This checks the 27 polynomial identities of one open rank-one chart.
theorem oppositeChart_adjoint (a b : F) (u v : Fin 4→F) (z : Fin 6→F) :
    adjoint (oppositeChart a b u v z)=0 := by
  apply Prod.ext
  · ext i; fin_cases i <;>
      simp [oppositeChart,oppositeA,oppositeB,oppositeC,oppositeDiagonalC,
        adjoint,SplitOctonion.norm,Matrix.vecHead,Matrix.vecTail] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [oppositeChart,oppositeA,oppositeB,oppositeC,oppositeDiagonalC,
        adjoint,SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
        SplitOctonion.unit,Matrix.vecHead,Matrix.vecTail] <;> ring

theorem oppositeChart_trace (a b : F) (u v : Fin 4→F) (z : Fin 6→F) :
    trace (oppositeChart a b u v z)=a+b+oppositeDiagonalC u v := rfl

def oppositeZeroChart (a : F) (u v : Fin 4→F) (z : Fin 6→F) : Carrier F :=
  oppositeChart a (-a-oppositeDiagonalC u v) u v z

theorem oppositeZeroChart_adjoint (a : F) (u v : Fin 4→F) (z : Fin 6→F) :
    adjoint (oppositeZeroChart a u v z)=0 := oppositeChart_adjoint _ _ _ _ _

theorem oppositeZeroChart_trace (a : F) (u v : Fin 4→F) (z : Fin 6→F) :
    trace (oppositeZeroChart a u v z)=0 := by
  rw [oppositeZeroChart,oppositeChart_trace]
  ring

theorem oppositeZeroChart_C7 (a : F) (u v : Fin 4→F) (z : Fin 6→F) :
    (oppositeZeroChart a u v z).2 2 7=1 := rfl

end Atlas.Albert

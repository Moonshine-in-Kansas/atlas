import Atlas.Algebra.SplitOctonion.Basic
import Atlas.LinearAlgebra.DotProductShell

/-! Independent counts for a nonzero value of the sum of two octonion norms. -/
namespace Atlas.SplitOctonion
variable {F : Type*} [Field F]

def pairHyperbolicCoordinates : (Carrier F × Carrier F) ≃
    ((Fin 8 → F) × (Fin 8 → F)) where
  toFun p :=
    (![p.1 0,p.1 1,p.1 2,p.1 3,p.2 0,p.2 1,p.2 2,p.2 3],
     ![p.1 7,p.1 6,p.1 5,p.1 4,p.2 7,p.2 6,p.2 5,p.2 4])
  invFun p :=
    (![p.1 0,p.1 1,p.1 2,p.1 3,p.2 3,p.2 2,p.2 1,p.2 0],
     ![p.1 4,p.1 5,p.1 6,p.1 7,p.2 7,p.2 6,p.2 5,p.2 4])
  left_inv p := by apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv p := by apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

theorem pairHyperbolicCoordinates_norm (p : Carrier F × Carrier F) :
    Atlas.DotProduct.functional (pairHyperbolicCoordinates p).1
      (pairHyperbolicCoordinates p).2 = norm p.1 + norm p.2 := by
  simp [Atlas.DotProduct.functional_apply,pairHyperbolicCoordinates,norm,
    Fin.sum_univ_succ]
  ring

def pairNormFiberEquiv (a : F) :
    {p : Carrier F × Carrier F // norm p.1 + norm p.2=a} ≃
      {p : (Fin 8 → F) × (Fin 8 → F) // Atlas.DotProduct.functional p.1 p.2=a} :=
  pairHyperbolicCoordinates.subtypeEquiv (fun p => by rw [pairHyperbolicCoordinates_norm])

theorem card_pairNorm_nonzero [Finite F] (a : F) (ha : a ≠ 0) :
    Nat.card {p : Carrier F × Carrier F // norm p.1 + norm p.2=a} =
      (Nat.card F ^ 8 - 1) * Nat.card F ^ 7 := by
  rw [Nat.card_congr (pairNormFiberEquiv a)]
  exact Atlas.DotProduct.card_nonzero_shell a ha

end Atlas.SplitOctonion

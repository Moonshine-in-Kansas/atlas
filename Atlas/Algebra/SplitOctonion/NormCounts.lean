import Atlas.Algebra.SplitOctonion.Basic
import Atlas.LinearAlgebra.DotProductZeroShell

/-! Split octonion norm fibres counted without a group action. -/
namespace Atlas.SplitOctonion
variable {F : Type*} [Field F]

def hyperbolicCoordinates : Carrier F ≃ ((Fin 4 → F) × (Fin 4 → F)) where
  toFun x := (![x 0,x 1,x 2,x 3],![x 7,x 6,x 5,x 4])
  invFun p := ![p.1 0,p.1 1,p.1 2,p.1 3,p.2 3,p.2 2,p.2 1,p.2 0]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv p := by apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

theorem hyperbolicCoordinates_norm (x : Carrier F) :
    Atlas.DotProduct.functional (hyperbolicCoordinates x).1
      (hyperbolicCoordinates x).2 = norm x := by
  simp [Atlas.DotProduct.functional_apply,hyperbolicCoordinates,norm,Fin.sum_univ_succ]
  ring

def normFiberEquiv (a : F) : {x : Carrier F // norm x=a} ≃
    {p : (Fin 4 → F) × (Fin 4 → F) // Atlas.DotProduct.functional p.1 p.2=a} :=
  hyperbolicCoordinates.subtypeEquiv (fun x => by rw [hyperbolicCoordinates_norm])

theorem card_norm_nonzero [Finite F] (a : F) (ha : a≠0) :
    Nat.card {x : Carrier F // norm x=a} = (Nat.card F ^ 4 - 1) * Nat.card F ^ 3 := by
  rw [Nat.card_congr (normFiberEquiv a)]
  exact Atlas.DotProduct.card_nonzero_shell a ha

theorem card_norm_zero [Finite F] :
    Nat.card {x : Carrier F // norm x=0} =
      Nat.card F ^ 4 + (Nat.card F ^ 4 - 1) * Nat.card F ^ 3 := by
  rw [Nat.card_congr (normFiberEquiv 0)]
  exact Atlas.DotProduct.card_zero_shell

end Atlas.SplitOctonion

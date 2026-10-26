import Atlas.LinearAlgebra.DotProductShell

namespace Atlas.DotProduct
variable {n : ℕ} {F : Type*} [Field F]

theorem card_zero_shell [Finite F] :
    Nat.card {p : (Fin n → F) × (Fin n → F) // functional p.1 p.2 = 0} =
      Nat.card F ^ n + (Nat.card F ^ n - 1) * Nat.card F ^ (n-1) := by
  classical
  letI := Fintype.ofFinite F
  rw [Nat.card_congr (shellFiberEquiv 0),Nat.card_sigma]
  have hc (x : Fin n → F) : Nat.card {y // functional x y=0} =
      if x=0 then Nat.card F ^ n else Nat.card F ^ (n-1) := by
    split_ifs with hx
    · subst x; exact card_zeroFiber
    · exact card_fiber x hx 0
  simp_rw [hc]
  rw [Finset.sum_ite]
  have hz : (Finset.univ.filter fun x : Fin n → F => x=0) = {0} := by
    ext x; simp
  simp [hz,Finset.filter_ne',Nat.card_eq_fintype_card]

end Atlas.DotProduct

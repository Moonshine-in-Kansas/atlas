import Atlas.LinearGroups.ReeF4.RootGroupEquiv

/-! Explicit commutator identities in the actual two-parameter root group.
The central parameter line is central; the full center identification is not
assumed here. -/
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem shortRootPairEquiv_center_comm {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b d : F) :
    shortRootPairEquiv m hcard a b * shortRootPairEquiv m hcard 0 d =
      shortRootPairEquiv m hcard 0 d * shortRootPairEquiv m hcard a b := by
  rw [shortRootPairEquiv_mul, shortRootPairEquiv_mul]
  simp only [add_zero, zero_add, mul_zero, zero_mul, map_zero]
  rw [add_comm b d]

theorem shortRootPairEquiv_commutator {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b c d : F) :
    shortRootPairEquiv m hcard a b * shortRootPairEquiv m hcard c d *
        (shortRootPairEquiv m hcard a b)⁻¹ *
        (shortRootPairEquiv m hcard c d)⁻¹ =
      shortRootPairEquiv m hcard 0 (theta F m a*c+theta F m c*a) := by
  rw [shortRootPairEquiv_inv, shortRootPairEquiv_inv]
  repeat rw [shortRootPairEquiv_mul]
  have hfirst : a+c+a+c = 0 := by
    linear_combination (CharTwo.add_self_eq_zero a) + (CharTwo.add_self_eq_zero c)
  rw [hfirst]
  congr 1
  simp only [map_add]
  ring_nf
  have hthree : (3 : F) = 1 := by
    linear_combination (CharTwo.two_eq_zero (R := F))
  simp [CharTwo.two_eq_zero, hthree]

end Atlas.ReeF4

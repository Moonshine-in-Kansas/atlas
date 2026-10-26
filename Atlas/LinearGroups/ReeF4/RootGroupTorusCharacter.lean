import Atlas.LinearGroups.ReeF4.RootGroupMembership

/-! Scalar and residual torus
characters, with no use of the order or simplicity of the ambient group. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The first-root character for conjugation `t⁻¹ U t`. -/
def shortRootTorusScale {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (a b : Fˣ) : Fˣ :=
  (thetaNormEquiv hcard).symm (a / thetaUnits m b)

theorem shortRootTorusScale_norm {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (a b : Fˣ) :
    shortRootTorusScale hcard a b * thetaUnits m (shortRootTorusScale hcard a b) =
      a / thetaUnits m b :=
  (thetaNormEquiv hcard).apply_symm_apply _

theorem shortRootTorusScale_explicit {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (a b : Fˣ) :
    shortRootTorusScale hcard a b = thetaUnits m a / a * (thetaUnits m b / b^2) := by
  change thetaUnits m (a / thetaUnits m b) * (a / thetaUnits m b)⁻¹ = _
  rw [map_div, thetaUnits_square hcard]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ac_rfl

theorem torusEquiv_root_residual_decomposition {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b : Fˣ) :
    torusEquiv m a b =
      torusEquiv m (shortRootTorusScale hcard a b *
        thetaUnits m (shortRootTorusScale hcard a b)) 1 *
      torusEquiv m (thetaUnits m b) b := by
  rw [shortRootTorusScale_norm hcard]
  have h := (torusHom (F := F) m).map_mul
    (a / thetaUnits m b, 1) (thetaUnits m b, b)
  simpa [torusHom, div_mul_cancel] using h

theorem shortRootTorusScale_norm_one {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (u : Fˣ) : shortRootTorusScale hcard (u*thetaUnits m u) 1 = u := by
  unfold shortRootTorusScale
  simp only [map_one, div_one]
  exact (thetaNormEquiv hcard).symm_apply_apply u

theorem shortRootTorusScale_surjective {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Function.Surjective (fun p : Fˣ × Fˣ => shortRootTorusScale hcard p.1 p.2) := by
  intro u
  exact ⟨(u*thetaUnits m u,1),shortRootTorusScale_norm_one hcard u⟩

theorem shortRootTorusScale_binary (hcard : Nat.card F = 2^(2*0+1)) (a b : Fˣ) :
    shortRootTorusScale hcard a b = 1 := by
  have hc : Nat.card Fˣ = 1 := by rw [Nat.card_units, hcard]; norm_num
  letI : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.mp hc).1
  exact Subsingleton.elim _ _

end Atlas.ReeF4

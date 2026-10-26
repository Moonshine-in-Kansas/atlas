import Atlas.LinearGroups.ReeF4.RootGroupTorusFormulas
import Atlas.LinearGroups.ReeF4.RootGroupResidualGrading
import Atlas.LinearGroups.ReeF4.RootGroupTorusCharacter
import Atlas.LinearGroups.ReeF4.RootGroupMembership

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem parameter_val (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a : F) (w : TraceZero F) :
    (shortRootPairEquiv m hcard a 0 w).val =
      shortRootParameterFormula (theta F m).toRingHom a w.val := by
  simp only [shortRootPairEquiv_apply, shortRootPairLinear, Module.End.mul_apply,
    shortRootCenterLinear_zero, LinearMap.id_apply, shortRootParameterLinear_val]

private theorem center_val (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (b : F) (w : TraceZero F) :
    (shortRootPairEquiv m hcard 0 b w).val =
      shortRootCenterFormula (theta F m).toRingHom b w.val := by
  simp only [shortRootPairEquiv_apply, shortRootPairLinear, Module.End.mul_apply,
    shortRootParameterLinear_zero, LinearMap.id_apply, shortRootCenterLinear_val]

private theorem pair_factor (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F) :
    shortRootPairEquiv m hcard a b =
      shortRootPairEquiv m hcard a 0 * shortRootPairEquiv m hcard 0 b := by
  rw [shortRootPairEquiv_mul]
  simp only [add_zero, zero_add, mul_zero]

theorem rootParameter_graded_conjugation {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u : Fˣ) (a : F) :
    let D := rootDiagonalEquiv (shortRootGradingWeight u (thetaUnits m u))
    D⁻¹ * shortRootPairEquiv m hcard a 0 * D =
      shortRootPairEquiv m hcard ((u : F)*a) 0 := by
  dsimp only
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  change rootDiagonalFormula (fun r => (shortRootGradingWeight u (thetaUnits m u) r)⁻¹)
    ((shortRootPairEquiv m hcard a 0
      (rootDiagonalEquiv (shortRootGradingWeight u (thetaUnits m u)) w)).val) = _
  rw [parameter_val,parameter_val]
  exact shortRootParameterFormula_graded_conjugation (theta F m).toRingHom u a w.val

theorem rootCenter_graded_conjugation {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u : Fˣ) (b : F) :
    let D := rootDiagonalEquiv (shortRootGradingWeight u (thetaUnits m u))
    D⁻¹ * shortRootPairEquiv m hcard 0 b * D =
      shortRootPairEquiv m hcard 0 ((u : F)*theta F m (u : F)*b) := by
  dsimp only
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  change rootDiagonalFormula (fun r => (shortRootGradingWeight u (thetaUnits m u) r)⁻¹)
    ((shortRootPairEquiv m hcard 0 b
      (rootDiagonalEquiv (shortRootGradingWeight u (thetaUnits m u)) w)).val) = _
  rw [center_val,center_val]
  exact shortRootCenterFormula_graded_conjugation (theta F m).toRingHom u
    (SuzukiFamily.theta_square hcard (u : F)) b w.val

theorem rootParameter_residual_comm {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u v : Fˣ) (a : F) :
    Commute (rootDiagonalEquiv (shortRootResidualWeight u v))
      (shortRootPairEquiv m hcard a 0) := by
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  change rootDiagonalFormula (shortRootResidualWeight u v)
    ((shortRootPairEquiv m hcard a 0 w).val) =
      (shortRootPairEquiv m hcard a 0 (rootDiagonalEquiv (shortRootResidualWeight u v) w)).val
  rw [parameter_val,parameter_val]
  exact shortRootParameterFormula_residual_comm (theta F m).toRingHom a u v w.val

theorem rootCenter_residual_comm {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u v : Fˣ) (b : F) :
    Commute (rootDiagonalEquiv (shortRootResidualWeight u v))
      (shortRootPairEquiv m hcard 0 b) := by
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  change rootDiagonalFormula (shortRootResidualWeight u v)
    ((shortRootPairEquiv m hcard 0 b w).val) =
      (shortRootPairEquiv m hcard 0 b (rootDiagonalEquiv (shortRootResidualWeight u v) w)).val
  rw [center_val,center_val]
  exact shortRootCenterFormula_residual_comm (theta F m).toRingHom b u v w.val

-- The final group algebra is independent of every coordinate implementation.
theorem conjugate_product_of_commuting_residual
    {G : Type*} [Group G] (D R X Y X' Y' : G)
    (hX : D⁻¹ * X * D = X') (hY : D⁻¹ * Y * D = Y')
    (hRX : Commute R X') (hRY : Commute R Y') :
    (D*R)⁻¹ * (X*Y) * (D*R) = X'*Y' := by
  calc
    _ = R⁻¹ * ((D⁻¹ * X * D) * (D⁻¹ * Y * D)) * R := by group
    _ = R⁻¹ * (X'*Y') * R := by rw [hX,hY]
    _ = X'*Y' := by
      rw [mul_assoc, ← (hRX.mul_right hRY).eq]
      group

theorem torusEquiv_residual {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (b : Fˣ) :
    torusEquiv m (thetaUnits m b) b =
      rootDiagonalEquiv (shortRootResidualWeight b (thetaUnits m b)) := by
  unfold torusEquiv
  congr 1
  funext r
  rw [torusWeight_eq_twisted m (thetaUnits m) (thetaUnits m b) b
    (thetaUnits_apply m _) (thetaUnits_apply m _)]
  exact twistedTorusWeight_residual (thetaUnits m) b (thetaUnits_square hcard b) r

theorem torusEquiv_normalizes_shortRootPair {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b : Fˣ) (c d : F) :
    (torusEquiv m a b)⁻¹ * shortRootPairEquiv m hcard c d * torusEquiv m a b =
      shortRootPairEquiv m hcard ((shortRootTorusScale hcard a b : F)*c)
        ((shortRootTorusScale hcard a b : F)*
          theta F m (shortRootTorusScale hcard a b : F)*d) := by
  let u := shortRootTorusScale hcard a b
  have hD : torusEquiv m (u*thetaUnits m u) 1 =
      rootDiagonalEquiv (shortRootGradingWeight u (thetaUnits m u)) := by
    unfold torusEquiv
    congr 1
    funext r
    exact torusWeight_normParameter hcard u r
  rw [torusEquiv_root_residual_decomposition hcard a b]
  change ((torusEquiv m (u*thetaUnits m u) 1 * torusEquiv m (thetaUnits m b) b)⁻¹ *
    shortRootPairEquiv m hcard c d *
    (torusEquiv m (u*thetaUnits m u) 1 * torusEquiv m (thetaUnits m b) b)) = _
  rw [hD,torusEquiv_residual hcard b]
  rw [pair_factor m hcard c d, pair_factor m hcard ((u : F)*c)
    ((u : F)*theta F m (u : F)*d)]
  exact conjugate_product_of_commuting_residual _ _ _ _ _ _
    (rootParameter_graded_conjugation hcard u c)
    (rootCenter_graded_conjugation hcard u d)
    (rootParameter_residual_comm hcard b (thetaUnits m b) _)
    (rootCenter_residual_comm hcard b (thetaUnits m b) _)

theorem torusEquiv_conjugate_shortRoot_mem {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b : Fˣ)
    (g : TraceZero F ≃ₗ[F] TraceZero F) (hg : g ∈ shortRootSubgroup m hcard) :
    (torusEquiv m a b)⁻¹ * g * torusEquiv m a b ∈ shortRootSubgroup m hcard := by
  rcases hg with ⟨⟨c,d⟩,rfl⟩
  rw [torusEquiv_normalizes_shortRootPair hcard a b c d]
  exact ⟨((shortRootTorusScale hcard a b : F)*c,
    (shortRootTorusScale hcard a b : F)*theta F m (shortRootTorusScale hcard a b : F)*d),rfl⟩

theorem torusEquiv_mem_shortRoot_normalizer {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b : Fˣ) :
    torusEquiv m a b ∈ Subgroup.normalizer (shortRootSubgroup m hcard) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro g
  constructor
  · exact torusEquiv_conjugate_shortRoot_mem hcard a b g
  · intro hg
    have hi : torusEquiv m a⁻¹ b⁻¹ = (torusEquiv m a b)⁻¹ :=
      (torusHom (F := F) m).map_inv (a,b)
    have hmem := torusEquiv_conjugate_shortRoot_mem hcard a⁻¹ b⁻¹ _ hg
    rw [hi,inv_inv] at hmem
    have he : torusEquiv m a b *
        ((torusEquiv m a b)⁻¹*g*torusEquiv m a b) * (torusEquiv m a b)⁻¹ = g := by group
    rwa [he] at hmem

end Atlas.ReeF4



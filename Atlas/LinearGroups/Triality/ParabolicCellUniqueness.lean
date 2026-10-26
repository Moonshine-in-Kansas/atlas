import Atlas.LinearGroups.Triality.ParabolicRootCells

/-! Uniqueness of the simple-root parameter in each parabolic cell. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

set_option maxHeartbeats 2000000 in
-- Compare eight explicit coordinates, with no characteristic restriction.
theorem shortRoot_weyl_intertwine (t : K) :
    shortRoot F K t * shortWeyl F K = shortWeyl F K * shortNegativeRoot F K (-t) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [Subgroup.coe_mul, LinearEquiv.mul_apply, shortWeyl_apply,
      shortRoot, shortNegativeRoot, pinnedRoot, pinnedNegativeRoot,
      differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply, e, f, Algebra.smul_def] <;> ring

theorem shortWeyl_inv_conjugate (t : K) :
    (shortWeyl F K)⁻¹ * shortRoot F K t * shortWeyl F K = shortNegativeRoot F K (-t) := by
  rw [mul_assoc, shortRoot_weyl_intertwine, inv_mul_cancel_left]

theorem shortNegativeRoot_borel_zero (hdeg : Module.finrank F K = 3) (t : K)
    (ht : shortNegativeRoot F K t ∈ borel F K hdeg) : t = 0 := by
  have hs : borel F K hdeg ≤ spaceStabilizer K (firstLine K) := by
    rw [borel_eq_sup]
    exact sup_le (unipotent_stabilizes_line F K hdeg) (torus_stabilizes_line F K)
  have he : (e (0 : Fin 4) : VectorD 4 K) ∈ firstLine K := Submodule.subset_span (by simp)
  have hz := firstLine_coordinate_one_zero K ((spaceStabilizer_mem K _ _).mp (hs ht) _ he)
  simpa [shortNegativeRoot, pinnedNegativeRoot, Subgroup.coe_mul, LinearEquiv.mul_apply,
    differenceRoot_apply, negativeSumRoot_apply, e, f, Algebra.smul_def] using hz

theorem shortCell_injective (hdeg : Module.finrank F K = 3) :
    Function.Injective (fun p : K × borel F K hdeg =>
      shortRoot F K p.1 * shortWeyl F K * p.2.val) := by
  rintro ⟨t,b⟩ ⟨u,c⟩ he
  change shortRoot F K t * shortWeyl F K * b.val = shortRoot F K u * shortWeyl F K * c.val at he
  have hx : shortRoot F K (-u) * shortRoot F K u = 1 := by
    rw [← shortRoot_add, neg_add_cancel, shortRoot_zero]
  have hh : shortNegativeRoot F K (-(-u+t)) = c.val * b.val⁻¹ := by
    calc
      _ = (shortWeyl F K)⁻¹ * (shortRoot F K (-u) * shortRoot F K t) * shortWeyl F K := by
        rw [← shortRoot_add, shortWeyl_inv_conjugate]
      _ = (shortWeyl F K)⁻¹ * shortRoot F K (-u) *
          (shortRoot F K t * shortWeyl F K * b.val) * b.val⁻¹ := by group
      _ = (shortWeyl F K)⁻¹ * shortRoot F K (-u) *
          (shortRoot F K u * shortWeyl F K * c.val) * b.val⁻¹ := by rw [he]
      _ = (shortWeyl F K)⁻¹ * (shortRoot F K (-u) * shortRoot F K u) *
          shortWeyl F K * c.val * b.val⁻¹ := by group
      _ = _ := by rw [hx]; group
  have hm : shortNegativeRoot F K (-(-u+t)) ∈ borel F K hdeg := by
    rw [hh]
    exact Subgroup.mul_mem _ c.property ((borel F K hdeg).inv_mem b.property)
  have htu := shortNegativeRoot_borel_zero F K hdeg _ hm
  have htu' : t = u := by linear_combination -htu
  subst u
  have hbc : b = c := Subtype.ext (mul_left_cancel he)
  exact Prod.ext rfl hbc

set_option maxHeartbeats 2000000 in
-- Compare eight explicit coordinates, with no characteristic restriction.
theorem longRoot_weyl_intertwine (t : F) :
    longRoot F K t * longWeyl F K = longWeyl F K * longNegativeRoot F K (-t) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [Subgroup.coe_mul, LinearEquiv.mul_apply, longWeyl_apply,
      longRoot, longNegativeRoot, pinnedRoot, pinnedNegativeRoot,
      differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply, e, f, Algebra.smul_def] <;> ring

theorem longWeyl_inv_conjugate (t : F) :
    (longWeyl F K)⁻¹ * longRoot F K t * longWeyl F K = longNegativeRoot F K (-t) := by
  rw [mul_assoc, longRoot_weyl_intertwine, inv_mul_cancel_left]

theorem longNegativeRoot_borel_zero (hdeg : Module.finrank F K = 3) (t : F)
    (ht : longNegativeRoot F K t ∈ borel F K hdeg) : t = 0 := by
  have hs : borel F K hdeg ≤ spaceStabilizer K (firstPlane K) := by
    rw [borel_eq_sup]
    exact sup_le (unipotent_stabilizes_plane F K hdeg) (torus_stabilizes_plane F K)
  have he : (e (1 : Fin 4) : VectorD 4 K) ∈ firstPlane K := Submodule.subset_span (by simp)
  have hz := firstPlane_coordinate_two_zero K ((spaceStabilizer_mem K _ _).mp (hs ht) _ he)
  simpa [longNegativeRoot, pinnedNegativeRoot, Subgroup.coe_mul, LinearEquiv.mul_apply,
    differenceRoot_apply, negativeSumRoot_apply, e, f, Algebra.smul_def] using hz

theorem longCell_injective (hdeg : Module.finrank F K = 3) :
    Function.Injective (fun p : F × borel F K hdeg =>
      longRoot F K p.1 * longWeyl F K * p.2.val) := by
  rintro ⟨t,b⟩ ⟨u,c⟩ he
  change longRoot F K t * longWeyl F K * b.val = longRoot F K u * longWeyl F K * c.val at he
  have hx : longRoot F K (-u) * longRoot F K u = 1 := by
    rw [← longRoot_add, neg_add_cancel, longRoot_zero]
  have hh : longNegativeRoot F K (-(-u+t)) = c.val * b.val⁻¹ := by
    calc
      _ = (longWeyl F K)⁻¹ * (longRoot F K (-u) * longRoot F K t) * longWeyl F K := by
        rw [← longRoot_add, longWeyl_inv_conjugate]
      _ = (longWeyl F K)⁻¹ * longRoot F K (-u) *
          (longRoot F K t * longWeyl F K * b.val) * b.val⁻¹ := by group
      _ = (longWeyl F K)⁻¹ * longRoot F K (-u) *
          (longRoot F K u * longWeyl F K * c.val) * b.val⁻¹ := by rw [he]
      _ = (longWeyl F K)⁻¹ * (longRoot F K (-u) * longRoot F K u) *
          longWeyl F K * c.val * b.val⁻¹ := by group
      _ = _ := by rw [hx]; group
  have hm : longNegativeRoot F K (-(-u+t)) ∈ borel F K hdeg := by
    rw [hh]
    exact Subgroup.mul_mem _ c.property ((borel F K hdeg).inv_mem b.property)
  have htu := longNegativeRoot_borel_zero F K hdeg _ hm
  have htu' : t = u := by linear_combination -htu
  subst u
  have hbc : b = c := Subtype.ext (mul_left_cancel he)
  exact Prod.ext rfl hbc

end Atlas.Triality

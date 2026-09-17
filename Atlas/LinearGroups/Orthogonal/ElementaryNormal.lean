import Atlas.LinearGroups.Orthogonal.Elementary

/-! # Normality of the actual elementary orthogonal subgroup -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- Conjugation carries actual Siegel generators to their transported parameters. -/
theorem siegelElement_conj (g : isometrySubgroup Q) (u v : V)
    (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    g * siegelElement Q u v hu huv * g⁻¹ =
      siegelElement Q (g.val u) (g.val v)
        ((isometryCarrierEquiv Q g).map_app u |>.trans hu)
        ((isometry_polar Q (isometryCarrierEquiv Q g) u v).trans huv) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val (siegel Q u v (g.val.symm x)) = siegel Q (g.val u) (g.val v) x
  have h := siegel_covariant Q (isometryCarrierEquiv Q g) u v (g.val.symm x)
  change g.val (siegel Q u v (g.val.symm x)) =
    siegel Q (g.val u) (g.val v) (g.val (g.val.symm x)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

instance elementarySubgroup_normal : (elementarySubgroup Q).Normal := by
  constructor
  intro x hx g
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, v, hu, huv, rfl⟩ := hx
    rw [siegelElement_conj]
    exact siegelElement_mem _ _ _ _ _
  | one => simpa using (elementarySubgroup Q).one_mem
  | mul x y hx hy ihx ihy =>
    have he : g * (x*y) * g⁻¹ = (g*x*g⁻¹) * (g*y*g⁻¹) := by group
    rw [he]
    exact (elementarySubgroup Q).mul_mem ihx ihy
  | inv x hx ih =>
    have he : g * x⁻¹ * g⁻¹ = (g*x*g⁻¹)⁻¹ := by group
    rw [he]
    exact (elementarySubgroup Q).inv_mem ih

end Atlas.Orthogonal

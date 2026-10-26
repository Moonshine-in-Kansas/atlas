import Atlas.LinearGroups.SL2Bruhat
import Atlas.LinearGroups.Triality.TorusRankOne
import Atlas.LinearGroups.Triality.ParabolicBasic

/-! Nonzero lower-root rewrites transported through the actual SL₂ maps. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem shortNegativeRoot_bruhat (a : Kˣ) :
    shortNegativeRoot F K (a : K) = shortRoot F K (↑a⁻¹ : K) *
      torusMap F K (-a⁻¹,1) * shortWeyl F K * shortRoot F K (↑a⁻¹ : K) := by
  have h := congrArg (rankOneShortOrthogonal F K) (Matrix.SL2.lower_bruhat a)
  have hd := short_diagonal_torus F K (-a⁻¹)
  simp only [diagonalSL] at hd
  simpa only [map_mul, rankOneShortOrthogonal_upper, rankOneShortOrthogonal_lower,
    hd, shortWeyl] using h

theorem longNegativeRoot_bruhat (a : Fˣ) :
    longNegativeRoot F K (a : F) = longRoot F K (↑a⁻¹ : F) *
      torusMap F K (1,-a⁻¹) * longWeyl F K * longRoot F K (↑a⁻¹ : F) := by
  have h := congrArg (rankOneLongOrthogonal F K) (Matrix.SL2.lower_bruhat a)
  have hd := long_diagonal_torus F K (-a⁻¹)
  simp only [diagonalSL] at hd
  simpa only [map_mul, rankOneLongOrthogonal_upper, rankOneLongOrthogonal_lower,
    hd, longWeyl] using h

theorem shortNegativeRoot_mem_parabolic (hdeg : Module.finrank F K = 3) (a : K) :
    shortNegativeRoot F K a ∈ shortParabolic F K hdeg := by
  by_cases ha : a = 0
  · simp [ha]
  let u : Kˣ := Units.mk0 a ha
  rw [show a = (u : K) from rfl, shortNegativeRoot_bruhat]
  have hr : shortRoot F K (↑u⁻¹ : K) ∈ shortParabolic F K hdeg := by
    apply (le_sup_left : borel F K hdeg ≤ shortParabolic F K hdeg)
    apply unipotent_le_borel F K hdeg
    exact ⟨⟨↑u⁻¹,0,0,0,0,0⟩, positiveMatrix_short F K _⟩
  have ht : torusMap F K (-u⁻¹,1) ∈ shortParabolic F K hdeg :=
    (le_sup_left : borel F K hdeg ≤ shortParabolic F K hdeg)
      (torus_le_borel F K hdeg ⟨_,rfl⟩)
  have hw : shortWeyl F K ∈ shortParabolic F K hdeg :=
    (le_sup_right : Subgroup.closure {shortWeyl F K} ≤ shortParabolic F K hdeg)
      (Subgroup.subset_closure (Set.mem_singleton _))
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hr ht) hw) hr

theorem longNegativeRoot_mem_parabolic (hdeg : Module.finrank F K = 3) (a : F) :
    longNegativeRoot F K a ∈ longParabolic F K hdeg := by
  by_cases ha : a = 0
  · simp [ha]
  let u : Fˣ := Units.mk0 a ha
  rw [show a = (u : F) from rfl, longNegativeRoot_bruhat]
  have hr : longRoot F K (↑u⁻¹ : F) ∈ longParabolic F K hdeg := by
    apply (le_sup_left : borel F K hdeg ≤ longParabolic F K hdeg)
    apply unipotent_le_borel F K hdeg
    exact ⟨⟨0,↑u⁻¹,0,0,0,0⟩, positiveMatrix_long F K _⟩
  have ht : torusMap F K (1,-u⁻¹) ∈ longParabolic F K hdeg :=
    (le_sup_left : borel F K hdeg ≤ longParabolic F K hdeg)
      (torus_le_borel F K hdeg ⟨_,rfl⟩)
  have hw : longWeyl F K ∈ longParabolic F K hdeg :=
    (le_sup_right : Subgroup.closure {longWeyl F K} ≤ longParabolic F K hdeg)
      (Subgroup.subset_closure (Set.mem_singleton _))
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hr ht) hw) hr

end Atlas.Triality

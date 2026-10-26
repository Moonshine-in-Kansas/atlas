import Atlas.LinearGroups.Unitary.ThreeTorusGeneration

/-! The rank-three root group is recovered from its central roots and the actual
base-torus commutators. Choosing t≠0,1 requires q>2 in the later application. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem three_torus_commutator (t : K) (ht : t ≠ 0)
    (hfix : conjugation F K t = t) (a b : K) :
    torusThreeMatrix t * rootThreeMatrix (F := F) a b * torusThreeMatrix t⁻¹ *
      rootThreeMatrix (F := F) (-a) (-b-a*conjugation F K a) =
      rootThreeMatrix (F := F) ((t-1)*a)
        ((t^2-1)*b+(t-1)*a*conjugation F K a) := by
  rw [torusThree_root_conjugation t ht hfix, rootThreeMatrix_mul]
  simp only [map_mul, hfix]
  congr 1 <;> ring

/-- Parameter validity of the displayed torus commutator, uniformly in characteristic. -/
theorem three_torus_commutator_condition (hdeg : Module.finrank F K = 2) (t : K)
    (hfix : conjugation F K t = t) (a b : K)
    (hab : rootThreeCondition (F := F) a b) :
    rootThreeCondition (F := F) ((t-1)*a)
      ((t^2-1)*b+(t-1)*a*conjugation F K a) := by
  dsimp [rootThreeCondition] at *
  simp only [map_mul, map_sub, map_add, map_pow, map_one, hfix, conjugation_conjugation hdeg]
  linear_combination (t^2-1)*hab


/-- A submonoid containing the central roots and all displayed torus commutators
contains the entire root group. This isolates the exact normality application. -/
theorem rootThree_mem_of_center_commutators (hdeg : Module.finrank F K = 2)
    (H : Submonoid (Matrix (Fin 3) (Fin 3) K))
    (hcenter : ∀ z, z + conjugation F K z = 0 → rootThreeMatrix (F := F) 0 z ∈ H)
    (t : K) (ht : t ≠ 0) (ht1 : t ≠ 1) (hfix : conjugation F K t = t)
    (hcomm : ∀ a b, rootThreeCondition (F := F) a b →
      torusThreeMatrix t * rootThreeMatrix (F := F) a b * torusThreeMatrix t⁻¹ *
        rootThreeMatrix (F := F) (-a) (-b-a*conjugation F K a) ∈ H)
    (a b : K) (hab : rootThreeCondition (F := F) a b) : rootThreeMatrix (F := F) a b ∈ H := by
  let c := a / (t-1)
  obtain ⟨d, hcd⟩ := exists_rootThree_parameter hdeg c
  let e := (t^2-1)*d+(t-1)*c*conjugation F K c
  have heq : (t-1)*c = a := by
    dsimp [c]
    field_simp
  have hce : rootThreeCondition (F := F) a e := by
    rw [← heq]
    exact three_torus_commutator_condition hdeg t hfix c d hcd
  have he_mem : rootThreeMatrix (F := F) a e ∈ H := by
    have h := hcomm c d hcd
    rw [three_torus_commutator t ht hfix, heq] at h
    change rootThreeMatrix (F := F) a ((t^2-1)*d+(t-1)*c*conjugation F K c) ∈ H
    rw [heq]
    exact h
  have hz : (b-e) + conjugation F K (b-e) = 0 := by
    dsimp [rootThreeCondition] at hab hce
    rw [map_sub]
    linear_combination hab - hce
  have h := H.mul_mem he_mem (hcenter (b-e) hz)
  rw [rootThreeMatrix_mul] at h
  simpa using h
end Atlas.Unitary

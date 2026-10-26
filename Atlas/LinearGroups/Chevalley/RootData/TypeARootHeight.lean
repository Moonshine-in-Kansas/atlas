import Atlas.LinearGroups.Chevalley.RootData.TypeACoordinateWeyl
import Atlas.LinearGroups.Chevalley.RootData.RootInversionLength

/-! Root height and the actual length statistic of the existing type-A datum.
The positive roots are precisely increasing coordinate pairs. -/
noncomputable section
namespace Atlas.Chevalley.TypeAData
open Classical RootData

def coordinateHeight (n : ℕ) : Lattice n →ₗ[ℤ] ℤ where
  toFun x := ∑ k : Fin n, -(k.val : ℤ) * x k
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp [Finset.mul_sum, mul_left_comm]

theorem coordinateHeight_root {n : ℕ} (a : Root n) :
    coordinateHeight n (root a) = (a.val.2.val : ℤ) - (a.val.1.val : ℤ) := by
  have hs (i : Fin n) : coordinateHeight n (Pi.single i 1) = -(i.val : ℤ) := by
    change (∑ k : Fin n, -(k.val : ℤ) * (Pi.single i (1 : ℤ) : Lattice n) k) = _
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero]
    simp
  change coordinateHeight n (Pi.single a.val.1 1 - Pi.single a.val.2 1) = _
  rw [map_sub, hs, hs]
  ring

/-- The height is the literal coordinate difference, uniformly in the rank. -/
theorem root_height {r : ℕ} (a : Root (r + 1)) :
    (base r).height a = (a.val.2.val : ℤ) - (a.val.1.val : ℤ) := by
  obtain ⟨f, _, _, hf⟩ := (base r).exists_root_eq_sum_int a
  have hs (j : Root (r + 1)) (hj : j ∈ (base r).support) :
      coordinateHeight (r + 1) (root j) = 1 := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    simp [coordinateHeight_root, simpleRoot]
  calc
    (base r).height a = ∑ j ∈ (base r).support, f j :=
      (base r).height_eq_sum hf
    _ = coordinateHeight (r + 1) (root a) := by
      have h := congrArg (coordinateHeight (r + 1)) hf
      change coordinateHeight (r + 1) (root a) = _ at h
      rw [h]
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j hj
      change f j = f j * coordinateHeight (r + 1) (root j)
      rw [hs j hj, mul_one]
    _ = _ := coordinateHeight_root a

theorem isPos_iff_coordinate_lt {r : ℕ} (a : Root (r + 1)) :
    (base r).IsPos a ↔ a.val.1 < a.val.2 := by
  rw [(base r).isPos_iff, root_height, sub_pos]
  exact Int.ofNat_lt

/-- Actual Weyl length counts ordinary coordinate inversions, not an assumed statistic. -/
theorem coordinateWeylEquiv_length {r : ℕ} (e : Equiv.Perm (Fin (r + 1))) :
    rootWeylLength (pairing (r + 1)) (base r) (coordinateWeylEquiv (r + 1) e) =
      (Finset.univ.filter (fun a : Root (r + 1) =>
        a.val.1 < a.val.2 ∧ e a.val.2 < e a.val.1)).card := by
  rw [← rootInversionCount_eq_rootWeylLength]
  unfold rootInversionCount rootInversions
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, isPos_iff_coordinate_lt]
  change (a.val.1 < a.val.2 ∧ ¬ e a.val.1 < e a.val.2) ↔ _
  have hne : e a.val.1 ≠ e a.val.2 := e.injective.ne a.property
  omega

end Atlas.Chevalley.TypeAData

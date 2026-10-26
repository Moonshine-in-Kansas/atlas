import Atlas.LinearGroups.Chevalley.Comparison.TypeCSymplecticHom
import Atlas.LinearGroups.Symplectic.ElementaryGeneration
import Atlas.LinearAlgebra.SLAdjacentGeneration

/-! Surjectivity of the marked type-C map by actual elementary generation.
No order, center, perfectness, simplicity or recognition result is used. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeC
open Classical
open scoped Matrix

private theorem terminal_X_transvection (n : ℕ) (hn : 2 ≤ n + 1)
    (R : Type*) [CommRing R] (t : R) :
    symplecticHom n hn R
      (selectedWeightCompanionX (.C (n + 1) hn) R (Fin.last n) t) =
      Atlas.Symplectic.transvection (Atlas.Symplectic.e (Fin.last n)) (-t) := by
  apply Atlas.Symplectic.ext_action
  intro x
  rw [Atlas.Symplectic.smul_eq_mulVec, symplecticHom_X_long]
  rw [Atlas.Symplectic.transvection_apply, Atlas.Symplectic.form_e_right]
  funext k
  cases k <;>
    simp [longMatrix, Matrix.fromBlocks_mulVec, Matrix.single_mulVec,
      Atlas.Symplectic.e, Pi.single_apply, Function.update_apply, eq_comm, add_comm]

private theorem terminal_Y_transvection (n : ℕ) (hn : 2 ≤ n + 1)
    (R : Type*) [CommRing R] (t : R) :
    symplecticHom n hn R
      (selectedWeightCompanionY (.C (n + 1) hn) R (Fin.last n) t) =
      Atlas.Symplectic.transvection (Atlas.Symplectic.f (Fin.last n)) t := by
  apply Atlas.Symplectic.ext_action
  intro x
  rw [Atlas.Symplectic.smul_eq_mulVec, symplecticHom_Y_long]
  rw [Atlas.Symplectic.transvection_apply, Atlas.Symplectic.form_f_right]
  funext k
  cases k <;>
    simp [longMatrix, Matrix.fromBlocks_transpose, Matrix.fromBlocks_mulVec,
      Matrix.single_mulVec, Atlas.Symplectic.f, Pi.single_apply, Function.update_apply,
      eq_comm, add_comm]

/-- The complete contragredient SL block lies in the actual image. -/
theorem diagonalSL_mem_range (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) K) :
    Atlas.Symplectic.diagonalSLHom (n + 1) K g ∈ (symplecticHom n hn K).range := by
  let H := (symplecticHom n hn K).range
  let D := Atlas.Symplectic.diagonalSLHom (n + 1) K
  have htop : H.comap D = ⊤ := by
    apply Atlas.sl_eq_top_of_adjacent_transvections (show 1 ≤ n by omega)
    · intro i hij t
      change D (Matrix.SpecialLinearGroup.transvection hij t) ∈ H
      refine ⟨selectedWeightCompanionX (.C (n + 1) hn) K i.castSucc t, ?_⟩
      apply Subtype.ext
      exact (symplecticHom_X_short n hn K i t).trans
        (Atlas.Symplectic.pairedTransvection_matrix (n + 1) K hij t).symm
    · intro i hij t
      change D (Matrix.SpecialLinearGroup.transvection hij t) ∈ H
      refine ⟨selectedWeightCompanionY (.C (n + 1) hn) K i.castSucc t, ?_⟩
      apply Subtype.ext
      exact (symplecticHom_Y_short n hn K i t).trans
        (Atlas.Symplectic.pairedTransvection_matrix (n + 1) K hij t).symm
  exact show g ∈ H.comap D from htop.symm ▸ Subgroup.mem_top g

theorem pairedTransvection_mem_range (n : ℕ) (hn : 2 ≤ n + 1)
    (K : Type*) [Field K] (i j : Fin (n + 1)) (hij : i ≠ j) (t : K) :
    Atlas.Symplectic.pairedTransvection (n + 1) K hij t ∈ (symplecticHom n hn K).range :=
  diagonalSL_mem_range n hn K (Matrix.SpecialLinearGroup.transvection hij t)

private theorem pairedWeyl_mem_range (n : ℕ) (hn : 2 ≤ n + 1)
    (K : Type*) [Field K] (i j : Fin (n + 1)) (hij : i ≠ j) :
    Atlas.Symplectic.pairedWeyl (n + 1) K hij ∈ (symplecticHom n hn K).range :=
  (symplecticHom n hn K).range.mul_mem
    ((symplecticHom n hn K).range.mul_mem
      (pairedTransvection_mem_range n hn K i j hij 1)
      (pairedTransvection_mem_range n hn K j i (Ne.symm hij) (-1)))
    (pairedTransvection_mem_range n hn K i j hij 1)

theorem coordinateTransvections_mem_range (n : ℕ) (hn : 2 ≤ n + 1)
    (K : Type*) [Field K] (i : Fin (n + 1)) (a : K) :
    Atlas.Symplectic.transvection (Atlas.Symplectic.e i) a ∈ (symplecticHom n hn K).range ∧
    Atlas.Symplectic.transvection (Atlas.Symplectic.f i) a ∈ (symplecticHom n hn K).range := by
  let H := (symplecticHom n hn K).range
  have he : Atlas.Symplectic.transvection (Atlas.Symplectic.e (Fin.last n)) a ∈ H := by
    refine ⟨selectedWeightCompanionX (.C (n + 1) hn) K (Fin.last n) (-a), ?_⟩
    simpa only [neg_neg] using terminal_X_transvection n hn K (-a)
  have hf : Atlas.Symplectic.transvection (Atlas.Symplectic.f (Fin.last n)) a ∈ H :=
    ⟨selectedWeightCompanionY (.C (n + 1) hn) K (Fin.last n) a,
      terminal_Y_transvection n hn K a⟩
  by_cases hi : i = Fin.last n
  · subst i
    exact ⟨he,hf⟩
  · have hw := pairedWeyl_mem_range n hn K i (Fin.last n) hi
    constructor
    · rw [← Atlas.Symplectic.pairedWeyl_e (n + 1) K hi,
        ← Atlas.Symplectic.transvection_conjugate]
      exact H.mul_mem (H.mul_mem hw he) (H.inv_mem hw)
    · rw [← Atlas.Symplectic.pairedWeyl_f (n + 1) K hi,
        ← Atlas.Symplectic.transvection_conjugate]
      exact H.mul_mem (H.mul_mem hw hf) (H.inv_mem hw)

/-- The literal marked map is onto the existing Sp over every field. -/
theorem symplecticHom_surjective (n : ℕ) (hn : 2 ≤ n + 1)
    (K : Type*) [Field K] : Function.Surjective (symplecticHom n hn K) := by
  apply MonoidHom.range_eq_top.mp
  apply Atlas.Symplectic.eq_top_of_paired_and_axis
  · exact pairedTransvection_mem_range n hn K
  · intro i a
    exact (coordinateTransvections_mem_range n hn K i a).1
  · intro i a
    exact (coordinateTransvections_mem_range n hn K i a).2

end Atlas.Chevalley.Comparison.TypeC

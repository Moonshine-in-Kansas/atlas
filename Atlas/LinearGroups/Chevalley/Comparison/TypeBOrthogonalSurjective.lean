import Atlas.LinearGroups.Chevalley.Comparison.TypeBOrthogonalHom
import Atlas.LinearGroups.Orthogonal.OddDiagonalSL
import Atlas.LinearGroups.Orthogonal.OddOneAxisGeneration
import Atlas.LinearAlgebra.SLAdjacentGeneration

/-! The actual B spin-conjugation map is onto the established elementary odd
quadratic group, by adjacent SL and coordinate Siegel generation. No orders,
center equality, simplicity or recognition theorem enter this argument. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeB
open Atlas.Orthogonal
variable (n : ℕ) (hn : 2 ≤ n+1) (F : Type*) [Field F]

/-- All contragredient determinant-one blocks occur in the actual image. -/
theorem oddDiagonalSL_mem_range (g : Matrix.SpecialLinearGroup (Fin (n+1)) F) :
    oddDiagonalSLHom (n+1) F g ∈ (orthogonalHom n hn F).range := by
  let H := (orthogonalHom n hn F).range
  let D := oddDiagonalSLHom (n+1) F
  have htop : H.comap D = ⊤ := by
    apply Atlas.sl_eq_top_of_adjacent_transvections (show 1 ≤ n by omega)
    · intro i hij t
      change D (Matrix.SpecialLinearGroup.transvection hij t) ∈ H
      refine ⟨selectedWeightCompanionX (.B (n+1) hn) F i.castSucc t, ?_⟩
      exact (orthogonalHom_X_long n hn F i t).trans
        (oddDiagonalSLHom_transvection (n+1) F i.castSucc i.succ hij t).symm
    · intro i hij t
      change D (Matrix.SpecialLinearGroup.transvection hij t) ∈ H
      refine ⟨selectedWeightCompanionY (.B (n+1) hn) F i.castSucc t, ?_⟩
      exact (orthogonalHom_Y_long n hn F i t).trans
        (oddDiagonalSLHom_transvection (n+1) F i.succ i.castSucc hij t).symm
  exact show g ∈ H.comap D from htop.symm ▸ Subgroup.mem_top g

theorem oddLong_mem_range (i j : Fin (n+1)) (hij : i ≠ j) (t : F) :
    oddLong (n+1) F i j hij t ∈ (orthogonalHom n hn F).range := by
  rw [← oddDiagonalSLHom_transvection]
  exact oddDiagonalSL_mem_range n hn F _

/-- Equality with the original elementary subgroup; not the full O_B. -/
theorem orthogonalHom_range :
    (orthogonalHom n hn F).range = elementarySubgroup (formB (n+1) F) := by
  apply le_antisymm
  · rintro g ⟨x,rfl⟩
    exact orthogonalHom_mem_elementary n hn F x
  · apply elementary_le_of_odd_long_and_one_axis (n+1) F hn
      (orthogonalHom n hn F).range (Fin.last n)
    · exact oddLong_mem_range n hn F
    · intro t
      exact ⟨selectedWeightCompanionX (.B (n+1) hn) F (Fin.last n) t,
        orthogonalHom_X_short n hn F t⟩
    · intro t
      exact ⟨selectedWeightCompanionY (.B (n+1) hn) F (Fin.last n) t,
        orthogonalHom_Y_short n hn F t⟩

/-- Surjectivity is proved from the concrete marked map over every field. -/
theorem elementaryHom_surjective : Function.Surjective (elementaryHom n hn F) := by
  intro y
  have hy : y.val ∈ (orthogonalHom n hn F).range :=
    (orthogonalHom_range n hn F).symm ▸ y.prop
  obtain ⟨x,hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

end Atlas.Chevalley.Comparison.TypeB

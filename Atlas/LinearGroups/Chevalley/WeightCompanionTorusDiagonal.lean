import Atlas.LinearGroups.Chevalley.WeightCompanionTorusOrder

/-! Diagonal matrices for the literal companion torus. Only the structural
range parametrization from TorusOrder is used, together with the already
proved diagonal formulas on the actual adjoint and minuscule blocks. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Fintype κ]

/-- Every literal torus element is diagonal in the faithful companion matrix.
No weight-spanning, torus-order or global projection-kernel theorem is needed. -/
theorem weightCompanionTorus_matrix_offDiagonal_zero
    (g : WeightCompanion P b O hc hm R)
    (hg : g ∈ weightCompanionTorusSubgroup P b O hc hm R) :
    ∀ row col : WeightCompanionCoordinates P b O, row ≠ col →
      (weightCompanionMatrixRepresentation P b O hc hm R g).val row col = 0 := by
  rw [weightCompanionTorusSubgroup_eq_range] at hg
  obtain ⟨t, rfl⟩ := hg
  rintro ⟨a, r⟩ ⟨c, s⟩ hne
  by_cases hac : a = c
  · subst c
    have hrs : r ≠ s := by
      intro he
      apply hne
      exact congrArg (fun x => (⟨a, x⟩ : WeightCompanionCoordinates P b O)) he
    rw [weightCompanionMatrixRepresentation_block]
    cases a with
    | none =>
      change ((weightCompanionTorusProduct P b O hc hm R Finset.univ t).val.1).val.val r s = 0
      rw [weightCompanionTorusProduct_adjoint, adjointTorusProduct_matrix]
      exact Matrix.diagonal_apply_ne _ hrs
    | some k =>
      change ((weightCompanionTorusProduct P b O hc hm R Finset.univ t).val.2 k).val r s = 0
      rw [weightCompanionTorusProduct_minuscule]
      exact Matrix.diagonal_apply_ne _ hrs
  · exact weightCompanionMatrixRepresentation_off_block P b O hc hm R _ hac r s

end Atlas.Chevalley

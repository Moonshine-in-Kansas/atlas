import Atlas.LinearGroups.Chevalley.RootData.OddCartanRows

/-! Actual single-edge neighbours in D (rank at least four), E6, E7, E8 and F4.
Only the already identified Cartan matrices are used. -/

noncomputable section
namespace Atlas.Chevalley

/-- The existing uniform D row witness is a genuine single edge. -/
theorem D_cartan_single_edge_neighbours (r : ℕ) (hr : 4 ≤ r) (i : Fin r) :
    ∃ j : Fin r, j ≠ i ∧ CartanMatrix.D r i j = -1 ∧ CartanMatrix.D r j i = -1 := by
  obtain ⟨j, hodd⟩ := D_cartan_odd_rows r hr i
  have hvalues : CartanMatrix.D r i j = 2 ∨
      CartanMatrix.D r i j = -1 ∨ CartanMatrix.D r i j = 0 := by
    simp only [CartanMatrix.D, Matrix.of_apply]
    split_ifs <;> simp
  have hij : CartanMatrix.D r i j = -1 := by
    rcases hvalues with htwo | hneg | hzero
    · exact False.elim ((by decide : ¬ Odd (2 : ℤ)) (htwo ▸ hodd))
    · exact hneg
    · exact False.elim ((by decide : ¬ Odd (0 : ℤ)) (hzero ▸ hodd))
  refine ⟨j, ?_, hij, ((CartanMatrix.D_isSymm r).apply i j).trans hij⟩
  intro heq
  subst j
  norm_num [CartanMatrix.D] at hij

private theorem E6_cartan_single_edge_neighbours : ∀ i : Fin 6, ∃ j : Fin 6,
    j ≠ i ∧ CartanMatrix.E 6 i j = -1 ∧ CartanMatrix.E 6 j i = -1 := by
  intro i
  fin_cases i <;> decide

private theorem E7_cartan_single_edge_neighbours : ∀ i : Fin 7, ∃ j : Fin 7,
    j ≠ i ∧ CartanMatrix.E 7 i j = -1 ∧ CartanMatrix.E 7 j i = -1 := by
  intro i
  fin_cases i <;> decide

private theorem E8_cartan_single_edge_neighbours : ∀ i : Fin 8, ∃ j : Fin 8,
    j ≠ i ∧ CartanMatrix.E 8 i j = -1 ∧ CartanMatrix.E 8 j i = -1 := by
  intro i
  fin_cases i <;> decide

private theorem F4_cartan_single_edge_neighbours : ∀ i : Fin 4, ∃ j : Fin 4,
    j ≠ i ∧ F4Table.cartan i j = -1 ∧ F4Table.cartan j i = -1 := by
  intro i
  fin_cases i <;> decide

theorem D_base_single_edge_neighbours (n : ℕ) (hn : 2 ≤ n) :
    ∀ i : (ClassicalData.baseD n).support, ∃ j : (ClassicalData.baseD n).support,
      j ≠ i ∧ (ClassicalData.baseD n).cartanMatrix i j = -1 ∧
        (ClassicalData.baseD n).cartanMatrix j i = -1 := by
  intro i
  obtain ⟨k, rfl⟩ := (ClassicalData.baseDIndexEquiv n).surjective i
  obtain ⟨l, hne, hij, hji⟩ := D_cartan_single_edge_neighbours (n+2) (by omega) k
  refine ⟨ClassicalData.baseDIndexEquiv n l,
    (fun h => hne ((ClassicalData.baseDIndexEquiv n).injective h)), ?_, ?_⟩
  · rwa [ClassicalData.baseD_cartan]
  · rwa [ClassicalData.baseD_cartan]

theorem E6_base_single_edge_neighbours : ∀ i : E6Data.base.support,
    ∃ j : E6Data.base.support, j ≠ i ∧ E6Data.base.cartanMatrix i j = -1 ∧
      E6Data.base.cartanMatrix j i = -1 := by
  intro i
  obtain ⟨k, rfl⟩ := E6Data.baseIndexEquiv.surjective i
  obtain ⟨l, hne, hij, hji⟩ := E6_cartan_single_edge_neighbours k
  refine ⟨E6Data.baseIndexEquiv l,
    (fun h => hne (E6Data.baseIndexEquiv.injective h)), ?_, ?_⟩
  · rwa [E6Data.base_cartan]
  · rwa [E6Data.base_cartan]

theorem E7_base_single_edge_neighbours : ∀ i : E7Data.base.support,
    ∃ j : E7Data.base.support, j ≠ i ∧ E7Data.base.cartanMatrix i j = -1 ∧
      E7Data.base.cartanMatrix j i = -1 := by
  intro i
  obtain ⟨k, rfl⟩ := E7Data.baseIndexEquiv.surjective i
  obtain ⟨l, hne, hij, hji⟩ := E7_cartan_single_edge_neighbours k
  refine ⟨E7Data.baseIndexEquiv l,
    (fun h => hne (E7Data.baseIndexEquiv.injective h)), ?_, ?_⟩
  · rwa [E7Data.base_cartan]
  · rwa [E7Data.base_cartan]

theorem E8_base_single_edge_neighbours : ∀ i : E8Data.base.support,
    ∃ j : E8Data.base.support, j ≠ i ∧ E8Data.base.cartanMatrix i j = -1 ∧
      E8Data.base.cartanMatrix j i = -1 := by
  intro i
  obtain ⟨k, rfl⟩ := E8Data.baseIndexEquiv.surjective i
  obtain ⟨l, hne, hij, hji⟩ := E8_cartan_single_edge_neighbours k
  refine ⟨E8Data.baseIndexEquiv l,
    (fun h => hne (E8Data.baseIndexEquiv.injective h)), ?_, ?_⟩
  · rwa [E8Data.base_cartan]
  · rwa [E8Data.base_cartan]

theorem F4_base_single_edge_neighbours : ∀ i : F4Data.base.support,
    ∃ j : F4Data.base.support, j ≠ i ∧ F4Data.base.cartanMatrix i j = -1 ∧
      F4Data.base.cartanMatrix j i = -1 := by
  intro i
  obtain ⟨k, rfl⟩ := F4Data.baseIndexEquiv.surjective i
  obtain ⟨l, hne, hij, hji⟩ := F4_cartan_single_edge_neighbours k
  refine ⟨F4Data.baseIndexEquiv l,
    (fun h => hne (F4Data.baseIndexEquiv.injective h)), ?_, ?_⟩
  · rwa [F4Data.base_cartan]
  · rwa [F4Data.base_cartan]

private theorem indexed_single_edge_neighbours_of_base {r : ℕ} (D : BasedDatum r)
    (h : ∀ i : D.base.support, ∃ j : D.base.support,
      j ≠ i ∧ D.base.cartanMatrix i j = -1 ∧ D.base.cartanMatrix j i = -1) :
    ∀ i : Fin r, ∃ j : Fin r, j ≠ i ∧
      D.base.cartanMatrix (D.indexEquiv i) (D.indexEquiv j) = -1 ∧
      D.base.cartanMatrix (D.indexEquiv j) (D.indexEquiv i) = -1 := by
  intro i
  obtain ⟨j, hne, hij, hji⟩ := h (D.indexEquiv i)
  obtain ⟨k, rfl⟩ := D.indexEquiv.surjective j
  exact ⟨k, (fun heq => hne (congrArg D.indexEquiv heq)), hij, hji⟩

theorem D_model_single_edge_neighbours (r : ℕ) (hr : 4 ≤ r) :
    ∀ i : Fin r, ∃ j : Fin r, j ≠ i ∧
      (rootDatum (.D r hr)).base.cartanMatrix
        ((rootDatum (.D r hr)).indexEquiv i) ((rootDatum (.D r hr)).indexEquiv j) = -1 ∧
      (rootDatum (.D r hr)).base.cartanMatrix
        ((rootDatum (.D r hr)).indexEquiv j) ((rootDatum (.D r hr)).indexEquiv i) = -1 := by
  apply indexed_single_edge_neighbours_of_base (rootDatum (.D r hr))
  with_unfolding_all exact D_base_single_edge_neighbours (r-2) (by omega)

theorem E6_model_single_edge_neighbours : ∀ i : Fin 6, ∃ j : Fin 6, j ≠ i ∧
    (rootDatum .E6).base.cartanMatrix
      ((rootDatum .E6).indexEquiv i) ((rootDatum .E6).indexEquiv j) = -1 ∧
    (rootDatum .E6).base.cartanMatrix
      ((rootDatum .E6).indexEquiv j) ((rootDatum .E6).indexEquiv i) = -1 :=
  indexed_single_edge_neighbours_of_base (rootDatum .E6) E6_base_single_edge_neighbours

theorem E7_model_single_edge_neighbours : ∀ i : Fin 7, ∃ j : Fin 7, j ≠ i ∧
    (rootDatum .E7).base.cartanMatrix
      ((rootDatum .E7).indexEquiv i) ((rootDatum .E7).indexEquiv j) = -1 ∧
    (rootDatum .E7).base.cartanMatrix
      ((rootDatum .E7).indexEquiv j) ((rootDatum .E7).indexEquiv i) = -1 :=
  indexed_single_edge_neighbours_of_base (rootDatum .E7) E7_base_single_edge_neighbours

theorem E8_model_single_edge_neighbours : ∀ i : Fin 8, ∃ j : Fin 8, j ≠ i ∧
    (rootDatum .E8).base.cartanMatrix
      ((rootDatum .E8).indexEquiv i) ((rootDatum .E8).indexEquiv j) = -1 ∧
    (rootDatum .E8).base.cartanMatrix
      ((rootDatum .E8).indexEquiv j) ((rootDatum .E8).indexEquiv i) = -1 :=
  indexed_single_edge_neighbours_of_base (rootDatum .E8) E8_base_single_edge_neighbours

theorem F4_model_single_edge_neighbours : ∀ i : Fin 4, ∃ j : Fin 4, j ≠ i ∧
    (rootDatum .F4).base.cartanMatrix
      ((rootDatum .F4).indexEquiv i) ((rootDatum .F4).indexEquiv j) = -1 ∧
    (rootDatum .F4).base.cartanMatrix
      ((rootDatum .F4).indexEquiv j) ((rootDatum .F4).indexEquiv i) = -1 :=
  indexed_single_edge_neighbours_of_base (rootDatum .F4) F4_base_single_edge_neighbours

end Atlas.Chevalley

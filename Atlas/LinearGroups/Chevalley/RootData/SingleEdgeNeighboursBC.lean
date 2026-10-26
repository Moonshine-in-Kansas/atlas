import Atlas.LinearGroups.Chevalley.RootData.ClassicalBasesBC

/-! Source candidate: the single-edge part and terminal double edge of the
actual uniformly indexed B/C Cartan matrices. No group property is assumed. -/

namespace Atlas.Chevalley

/-- Every B node except the final short one has a single-edge neighbour
among the preceding nodes, uniformly in rank at least three. -/
theorem B_cartan_single_edge_neighbour_before_last
    (r : ℕ) (hr : 3 ≤ r) (i : Fin r) (hi : i.val + 1 < r) :
    ∃ j : Fin r, j ≠ i ∧ j.val + 1 < r ∧
      CartanMatrix.B r i j = -1 ∧ CartanMatrix.B r j i = -1 := by
  by_cases h0 : i.val = 0
  · refine ⟨⟨1, by omega⟩, ?_, by change 1 + 1 < r; omega, ?_, ?_⟩
    · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    all_goals
      simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> omega
  · refine ⟨⟨i.val - 1, by omega⟩, ?_, by change i.val - 1 + 1 < r; omega, ?_, ?_⟩
    · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    all_goals
      simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> omega

/-- The same preceding-node graph in C; the directed terminal edge is kept
separate and is not mistaken for a single edge. -/
theorem C_cartan_single_edge_neighbour_before_last
    (r : ℕ) (hr : 3 ≤ r) (i : Fin r) (hi : i.val + 1 < r) :
    ∃ j : Fin r, j ≠ i ∧ j.val + 1 < r ∧
      CartanMatrix.C r i j = -1 ∧ CartanMatrix.C r j i = -1 := by
  obtain ⟨j, hne, hj, hij, hji⟩ := B_cartan_single_edge_neighbour_before_last r hr i hi
  refine ⟨j, hne, hj, ?_, ?_⟩
  · simpa only [← CartanMatrix.B_transpose, Matrix.transpose_apply] using hji
  · simpa only [← CartanMatrix.B_transpose, Matrix.transpose_apply] using hij

/-- In B, the final short node has Cartan entry −1 toward the long node;
the reverse directed entry is −2. -/
theorem B_cartan_terminal_double_edge (r : ℕ) (hr : 2 ≤ r) :
    let a : Fin r := ⟨r - 1, by omega⟩
    let b : Fin r := ⟨r - 2, by omega⟩
    a ≠ b ∧ CartanMatrix.B r a b = -1 ∧ CartanMatrix.B r b a = -2 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
  all_goals
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> omega

/-- In C, the penultimate short node and final long node have the same
oriented double-edge entries as the pair above. -/
theorem C_cartan_terminal_double_edge (r : ℕ) (hr : 2 ≤ r) :
    let a : Fin r := ⟨r - 2, by omega⟩
    let b : Fin r := ⟨r - 1, by omega⟩
    a ≠ b ∧ CartanMatrix.C r a b = -1 ∧ CartanMatrix.C r b a = -2 := by
  obtain ⟨hne, hminus, htwo⟩ := B_cartan_terminal_double_edge r hr
  dsimp only at hne hminus htwo ⊢
  refine ⟨hne.symm, ?_, ?_⟩
  · simpa only [← CartanMatrix.B_transpose, Matrix.transpose_apply] using hminus
  · simpa only [← CartanMatrix.B_transpose, Matrix.transpose_apply] using htwo

/-- The single-edge property is supplied on the actual B base. -/
theorem B_base_single_edge_neighbour_before_last
    (n : ℕ) (hn : 2 ≤ n) (i : Fin (n + 1)) (hi : i.val < n) :
    ∃ j : Fin (n + 1), j ≠ i ∧ j.val < n ∧
      (ClassicalData.baseB n).cartanMatrix (ClassicalData.baseBIndexEquiv n i)
        (ClassicalData.baseBIndexEquiv n j) = -1 ∧
      (ClassicalData.baseB n).cartanMatrix (ClassicalData.baseBIndexEquiv n j)
        (ClassicalData.baseBIndexEquiv n i) = -1 := by
  obtain ⟨j, hne, hj, hij, hji⟩ :=
    B_cartan_single_edge_neighbour_before_last (n + 1) (by omega) i (by omega)
  exact ⟨j, hne, by omega, by rwa [ClassicalData.baseB_cartan],
    by rwa [ClassicalData.baseB_cartan]⟩

/-- The single-edge property is supplied on the actual C base. -/
theorem C_base_single_edge_neighbour_before_last
    (n : ℕ) (hn : 2 ≤ n) (i : Fin (n + 1)) (hi : i.val < n) :
    ∃ j : Fin (n + 1), j ≠ i ∧ j.val < n ∧
      (ClassicalData.baseC n).cartanMatrix (ClassicalData.baseCIndexEquiv n i)
        (ClassicalData.baseCIndexEquiv n j) = -1 ∧
      (ClassicalData.baseC n).cartanMatrix (ClassicalData.baseCIndexEquiv n j)
        (ClassicalData.baseCIndexEquiv n i) = -1 := by
  obtain ⟨j, hne, hj, hij, hji⟩ :=
    C_cartan_single_edge_neighbour_before_last (n + 1) (by omega) i (by omega)
  exact ⟨j, hne, by omega, by rwa [ClassicalData.baseC_cartan],
    by rwa [ClassicalData.baseC_cartan]⟩

end Atlas.Chevalley

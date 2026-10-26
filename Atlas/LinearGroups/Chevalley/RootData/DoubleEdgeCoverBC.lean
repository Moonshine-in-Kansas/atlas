import Atlas.LinearGroups.Chevalley.RootData.SingleEdgeNeighboursBC

/-! Uncompiled source candidate. Every actual B/C node in rank at least
three lies on a single edge or joins such a node by the terminal double
edge. This is a statement about the coordinate Cartan matrices and bases. -/

namespace Atlas.Chevalley

/-- The exact Cartan cover used by the double-edge normal propagation
argument, on the numbered type-B diagram. -/
theorem B_cartan_a2_double_cover (r : ℕ) (hr : 3 ≤ r) (i : Fin r) :
    (∃ j : Fin r, j ≠ i ∧ CartanMatrix.B r i j = -1 ∧
      CartanMatrix.B r j i = -1) ∨
    (∃ j k : Fin r, j ≠ i ∧ k ≠ j ∧
      CartanMatrix.B r j k = -1 ∧ CartanMatrix.B r k j = -1 ∧
      ((CartanMatrix.B r i j = -1 ∧ CartanMatrix.B r j i = -2) ∨
       (CartanMatrix.B r i j = -2 ∧ CartanMatrix.B r j i = -1))) := by
  by_cases hi : i.val + 1 < r
  · obtain ⟨j, hne, _, hij, hji⟩ :=
      B_cartan_single_edge_neighbour_before_last r hr i hi
    exact Or.inl ⟨j, hne, hij, hji⟩
  · have hi' : i = (⟨r - 1, by omega⟩ : Fin r) := Fin.ext (by change i.val = r - 1; omega)
    rw [hi']
    obtain ⟨hne, hminus, htwo⟩ := B_cartan_terminal_double_edge r (by omega)
    obtain ⟨k, hkj, _, hjk, hkj'⟩ :=
      B_cartan_single_edge_neighbour_before_last r hr
        (⟨r - 2, by omega⟩ : Fin r) (by simp only [Fin.val_mk]; omega)
    exact Or.inr ⟨⟨r - 2, by omega⟩, k, hne.symm, hkj, hjk, hkj',
      Or.inl ⟨hminus, htwo⟩⟩

/-- The same cover on type C. At the terminal node the double-edge
orientation is reversed, which is retained explicitly. -/
theorem C_cartan_a2_double_cover (r : ℕ) (hr : 3 ≤ r) (i : Fin r) :
    (∃ j : Fin r, j ≠ i ∧ CartanMatrix.C r i j = -1 ∧
      CartanMatrix.C r j i = -1) ∨
    (∃ j k : Fin r, j ≠ i ∧ k ≠ j ∧
      CartanMatrix.C r j k = -1 ∧ CartanMatrix.C r k j = -1 ∧
      ((CartanMatrix.C r i j = -1 ∧ CartanMatrix.C r j i = -2) ∨
       (CartanMatrix.C r i j = -2 ∧ CartanMatrix.C r j i = -1))) := by
  by_cases hi : i.val + 1 < r
  · obtain ⟨j, hne, _, hij, hji⟩ :=
      C_cartan_single_edge_neighbour_before_last r hr i hi
    exact Or.inl ⟨j, hne, hij, hji⟩
  · have hi' : i = (⟨r - 1, by omega⟩ : Fin r) := Fin.ext (by change i.val = r - 1; omega)
    rw [hi']
    obtain ⟨hne, hminus, htwo⟩ := C_cartan_terminal_double_edge r (by omega)
    obtain ⟨k, hkj, _, hjk, hkj'⟩ :=
      C_cartan_single_edge_neighbour_before_last r hr
        (⟨r - 2, by omega⟩ : Fin r) (by simp only [Fin.val_mk]; omega)
    exact Or.inr ⟨⟨r - 2, by omega⟩, k, hne, hkj, hjk, hkj',
      Or.inr ⟨htwo, hminus⟩⟩

/-- Transfer the numbered cover to the actual type-B root-subtype base.
The rank is `n + 1`, so the hypothesis is `2 ≤ n`. -/
theorem B_base_a2_double_cover (n : ℕ) (hn : 2 ≤ n) :
    ∀ i : (ClassicalData.baseB n).support,
      (∃ j : (ClassicalData.baseB n).support, j ≠ i ∧
        (ClassicalData.baseB n).cartanMatrix i j = -1 ∧
        (ClassicalData.baseB n).cartanMatrix j i = -1) ∨
      (∃ j k : (ClassicalData.baseB n).support, j ≠ i ∧ k ≠ j ∧
        (ClassicalData.baseB n).cartanMatrix j k = -1 ∧
        (ClassicalData.baseB n).cartanMatrix k j = -1 ∧
        (((ClassicalData.baseB n).cartanMatrix i j = -1 ∧
          (ClassicalData.baseB n).cartanMatrix j i = -2) ∨
         ((ClassicalData.baseB n).cartanMatrix i j = -2 ∧
          (ClassicalData.baseB n).cartanMatrix j i = -1))) := by
  intro a
  obtain ⟨i, rfl⟩ := (ClassicalData.baseBIndexEquiv n).surjective a
  rcases B_cartan_a2_double_cover (n + 1) (by omega) i with
      ⟨j, hne, hij, hji⟩ | ⟨j, k, hji, hkj, hjk, hkj', hedge⟩
  · exact Or.inl ⟨ClassicalData.baseBIndexEquiv n j,
      fun h => hne ((ClassicalData.baseBIndexEquiv n).injective h),
      by rwa [ClassicalData.baseB_cartan], by rwa [ClassicalData.baseB_cartan]⟩
  · refine Or.inr ⟨ClassicalData.baseBIndexEquiv n j,
      ClassicalData.baseBIndexEquiv n k,
      fun h => hji ((ClassicalData.baseBIndexEquiv n).injective h),
      fun h => hkj ((ClassicalData.baseBIndexEquiv n).injective h),
      ?_, ?_, ?_⟩
    · rwa [ClassicalData.baseB_cartan]
    · rwa [ClassicalData.baseB_cartan]
    · simpa only [ClassicalData.baseB_cartan] using hedge

/-- Transfer the numbered cover to the actual type-C root-subtype base. -/
theorem C_base_a2_double_cover (n : ℕ) (hn : 2 ≤ n) :
    ∀ i : (ClassicalData.baseC n).support,
      (∃ j : (ClassicalData.baseC n).support, j ≠ i ∧
        (ClassicalData.baseC n).cartanMatrix i j = -1 ∧
        (ClassicalData.baseC n).cartanMatrix j i = -1) ∨
      (∃ j k : (ClassicalData.baseC n).support, j ≠ i ∧ k ≠ j ∧
        (ClassicalData.baseC n).cartanMatrix j k = -1 ∧
        (ClassicalData.baseC n).cartanMatrix k j = -1 ∧
        (((ClassicalData.baseC n).cartanMatrix i j = -1 ∧
          (ClassicalData.baseC n).cartanMatrix j i = -2) ∨
         ((ClassicalData.baseC n).cartanMatrix i j = -2 ∧
          (ClassicalData.baseC n).cartanMatrix j i = -1))) := by
  intro a
  obtain ⟨i, rfl⟩ := (ClassicalData.baseCIndexEquiv n).surjective a
  rcases C_cartan_a2_double_cover (n + 1) (by omega) i with
      ⟨j, hne, hij, hji⟩ | ⟨j, k, hji, hkj, hjk, hkj', hedge⟩
  · exact Or.inl ⟨ClassicalData.baseCIndexEquiv n j,
      fun h => hne ((ClassicalData.baseCIndexEquiv n).injective h),
      by rwa [ClassicalData.baseC_cartan], by rwa [ClassicalData.baseC_cartan]⟩
  · refine Or.inr ⟨ClassicalData.baseCIndexEquiv n j,
      ClassicalData.baseCIndexEquiv n k,
      fun h => hji ((ClassicalData.baseCIndexEquiv n).injective h),
      fun h => hkj ((ClassicalData.baseCIndexEquiv n).injective h),
      ?_, ?_, ?_⟩
    · rwa [ClassicalData.baseC_cartan]
    · rwa [ClassicalData.baseC_cartan]
    · simpa only [ClassicalData.baseC_cartan] using hedge

end Atlas.Chevalley

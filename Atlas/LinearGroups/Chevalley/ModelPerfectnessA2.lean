import Atlas.LinearGroups.Chevalley.AdjointPerfectnessA2
import Atlas.LinearGroups.Chevalley.ModelOppositeSimple

/-! The actual all-type single-edge-neighbour interface and its uniform type-A
application. Other types must provide their actual Cartan neighbours separately. -/

noncomputable section
namespace Atlas.Chevalley
open Group

/-- The actual root-data dispatcher discharges the generic diamond premise.
The only remaining combinatorial input is expressed on its actual numbered base. -/
theorem model_isPerfect_of_a2_neighbours
    (Φ : RootType) (R : Type*) [CommRing R]
    (hrows : ∀ i : Fin Φ.rank, ∃ j : Fin Φ.rank, j ≠ i ∧
      (rootDatum Φ).base.cartanMatrix
        ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) = -1 ∧
      (rootDatum Φ).base.cartanMatrix
        ((rootDatum Φ).indexEquiv j) ((rootDatum Φ).indexEquiv i) = -1) :
    IsPerfect (Model Φ R) := by
  apply adjoint_isPerfect_of_a2_neighbours (rootDatum Φ).pairing
    (rootDatum Φ).base (rootDatum_simpleDiamondProducts Φ) R
  intro a
  obtain ⟨i, rfl⟩ := (rootDatum Φ).indexEquiv.surjective a
  obtain ⟨j, hne, hij, hji⟩ := hrows i
  exact ⟨(rootDatum Φ).indexEquiv j,
    fun h => hne ((rootDatum Φ).indexEquiv.injective h), hij, hji⟩

/-- Every node of the finite type-A chain with at least two nodes has a
distinct neighbour with Cartan entries -1 in both orientations. -/
theorem A_cartan_a2_neighbours (r : ℕ) (hr : 2 ≤ r) (i : Fin r) :
    ∃ j : Fin r, j ≠ i ∧ CartanMatrix.A r i j = -1 ∧ CartanMatrix.A r j i = -1 := by
  by_cases hzero : i.val = 0
  · refine ⟨⟨1, by omega⟩, ?_, ?_, ?_⟩
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_mk] at hv
      omega
    · simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> omega
    · simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> omega
  · refine ⟨⟨i.val - 1, by omega⟩, ?_, ?_, ?_⟩
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_mk] at hv
      omega
    · simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> omega
    · simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> omega

/-- Transfer the explicit type-A neighbours to the actual root-subtype base. -/
theorem A_base_a2_neighbours (r : ℕ) (hr : 2 ≤ r) :
    ∀ i : (TypeAData.base r).support, ∃ j : (TypeAData.base r).support,
      j ≠ i ∧ (TypeAData.base r).cartanMatrix i j = -1 ∧
        (TypeAData.base r).cartanMatrix j i = -1 := by
  intro a
  obtain ⟨i, rfl⟩ := (TypeAData.baseIndexEquiv r).surjective a
  obtain ⟨j, hne, hij, hji⟩ := A_cartan_a2_neighbours r hr i
  refine ⟨TypeAData.baseIndexEquiv r j,
    fun h => hne ((TypeAData.baseIndexEquiv r).injective h), ?_, ?_⟩
  · rwa [TypeAData.base_cartan]
  · rwa [TypeAData.base_cartan]

/-- The newly constructed type-A adjoint model is perfect over every
commutative ring in rank at least two, including the binary and ternary fields. -/
theorem model_A_isPerfect_of_rank_ge_two (r : ℕ) (hr : 2 ≤ r)
    (R : Type*) [CommRing R] :
    IsPerfect (Model (.A r (by omega)) R) := by
  apply adjoint_isPerfect_of_a2_neighbours
    (rootDatum (.A r (by omega))).pairing (rootDatum (.A r (by omega))).base
    (rootDatum_simpleDiamondProducts (.A r (by omega))) R
  with_unfolding_all exact A_base_a2_neighbours r hr

end Atlas.Chevalley

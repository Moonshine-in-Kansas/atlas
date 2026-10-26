import Atlas.LinearAlgebra.MatrixConnectivity
import Atlas.LinearGroups.Chevalley.Models

/-! Actual Cartan connectivity for every validated uniform root type.
Classical proofs are uniform in rank; the exceptional checks concern only
their six-, seven-, eight-, four-, and two-node integer matrices. -/
namespace Atlas.Chevalley
open Atlas.LinearAlgebra

theorem A_cartan_connected (r : ℕ) (hr : 0 < r) :
    MatrixAdjacencyConnected (CartanMatrix.A r) := by
  apply matrixAdjacencyConnected_of_descent _ (⟨0, hr⟩ : Fin r) Fin.val
  intro i hi
  have hi0 : 0 < i.val := by
    have : i.val ≠ 0 := fun h => hi (Fin.ext h)
    omega
  refine ⟨⟨i.val - 1, by omega⟩, by change i.val - 1 < i.val; omega, ?_, ?_⟩ <;>
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff] <;>
    split_ifs <;> omega

theorem B_cartan_connected (r : ℕ) (hr : 0 < r) :
    MatrixAdjacencyConnected (CartanMatrix.B r) := by
  apply matrixAdjacencyConnected_of_descent _ (⟨0, hr⟩ : Fin r) Fin.val
  intro i hi
  have hi0 : 0 < i.val := by
    have : i.val ≠ 0 := fun h => hi (Fin.ext h)
    omega
  refine ⟨⟨i.val - 1, by omega⟩, by change i.val - 1 < i.val; omega, ?_, ?_⟩ <;>
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff] <;>
    split_ifs <;> omega

theorem C_cartan_connected (r : ℕ) (hr : 0 < r) :
    MatrixAdjacencyConnected (CartanMatrix.C r) := by
  apply matrixAdjacencyConnected_of_descent _ (⟨0, hr⟩ : Fin r) Fin.val
  intro i hi
  have hi0 : 0 < i.val := by
    have : i.val ≠ 0 := fun h => hi (Fin.ext h)
    omega
  refine ⟨⟨i.val - 1, by omega⟩, by change i.val - 1 < i.val; omega, ?_, ?_⟩ <;>
    simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff] <;>
    split_ifs <;> omega

theorem D_cartan_connected (r : ℕ) (hr : 3 ≤ r) :
    MatrixAdjacencyConnected (CartanMatrix.D r) := by
  apply matrixAdjacencyConnected_of_descent _ (⟨0, by omega⟩ : Fin r) Fin.val
  intro i hi
  have hi0 : 0 < i.val := by
    have : i.val ≠ 0 := fun h => hi (Fin.ext h)
    omega
  by_cases hlast : i.val = r - 1
  · refine ⟨⟨r - 3, by omega⟩, by change r - 3 < i.val; omega, ?_, ?_⟩ <;>
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] <;>
      split_ifs <;> omega
  · refine ⟨⟨i.val - 1, by omega⟩, by change i.val - 1 < i.val; omega, ?_, ?_⟩ <;>
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] <;>
      split_ifs <;> omega

private def E_distance {r : ℕ} (i : Fin r) : ℕ :=
  if i.val = 0 then 2 else if i.val = 1 ∨ i.val = 2 then 1 else i.val - 3

theorem E6_cartan_connected : MatrixAdjacencyConnected (CartanMatrix.E 6) := by
  apply matrixAdjacencyConnected_of_descent (CartanMatrix.E 6) (3 : Fin 6) E_distance
  intro i hi
  fin_cases i
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨3, by decide⟩
  · exact False.elim (hi rfl)
  · exact ⟨3, by decide⟩
  · exact ⟨4, by decide⟩

theorem E7_cartan_connected : MatrixAdjacencyConnected (CartanMatrix.E 7) := by
  apply matrixAdjacencyConnected_of_descent (CartanMatrix.E 7) (3 : Fin 7) E_distance
  intro i hi
  fin_cases i
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨3, by decide⟩
  · exact False.elim (hi rfl)
  · exact ⟨3, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨5, by decide⟩

theorem E8_cartan_connected : MatrixAdjacencyConnected (CartanMatrix.E 8) := by
  apply matrixAdjacencyConnected_of_descent (CartanMatrix.E 8) (3 : Fin 8) E_distance
  intro i hi
  fin_cases i
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨3, by decide⟩
  · exact False.elim (hi rfl)
  · exact ⟨3, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨5, by decide⟩
  · exact ⟨6, by decide⟩

theorem F4_cartan_connected : MatrixAdjacencyConnected F4Table.cartan := by
  apply matrixAdjacencyConnected_of_descent F4Table.cartan (0 : Fin 4) Fin.val
  intro i hi
  fin_cases i
  · exact False.elim (hi rfl)
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩

theorem G2_cartan_connected : MatrixAdjacencyConnected G2Table.cartan := by
  apply matrixAdjacencyConnected_of_descent G2Table.cartan (0 : Fin 2) Fin.val
  intro i hi
  fin_cases i
  · exact False.elim (hi rfl)
  · exact ⟨0, by decide⟩

theorem A_base_cartan_connected (r : ℕ) (hr : 0 < r) :
    MatrixAdjacencyConnected (TypeAData.base r).cartanMatrix :=
  matrixAdjacencyConnected_reindex _ _ (TypeAData.baseIndexEquiv r)
    (TypeAData.base_cartan r) (A_cartan_connected r hr)

theorem B_base_cartan_connected (n : ℕ) :
    MatrixAdjacencyConnected (ClassicalData.baseB n).cartanMatrix :=
  matrixAdjacencyConnected_reindex _ _ (ClassicalData.baseBIndexEquiv n)
    (ClassicalData.baseB_cartan n) (B_cartan_connected (n + 1) (by omega))

theorem C_base_cartan_connected (n : ℕ) :
    MatrixAdjacencyConnected (ClassicalData.baseC n).cartanMatrix :=
  matrixAdjacencyConnected_reindex _ _ (ClassicalData.baseCIndexEquiv n)
    (ClassicalData.baseC_cartan n) (C_cartan_connected (n + 1) (by omega))

theorem D_base_cartan_connected (n : ℕ) (hn : 1 ≤ n) :
    MatrixAdjacencyConnected (ClassicalData.baseD n).cartanMatrix :=
  matrixAdjacencyConnected_reindex _ _ (ClassicalData.baseDIndexEquiv n)
    (ClassicalData.baseD_cartan n) (D_cartan_connected (n + 2) (by omega))

theorem rootDatum_cartan_connected (Φ : RootType) :
    MatrixAdjacencyConnected (rootDatum Φ).base.cartanMatrix := by
  cases Φ with
  | A r hr => exact A_base_cartan_connected r (by omega)
  | B r hr => exact B_base_cartan_connected (r - 1)
  | C r hr => exact C_base_cartan_connected (r - 1)
  | D r hr => exact D_base_cartan_connected (r - 2) (by omega)
  | E6 =>
      change MatrixAdjacencyConnected E6Data.base.cartanMatrix
      exact matrixAdjacencyConnected_reindex (CartanMatrix.E 6) E6Data.base.cartanMatrix
        E6Data.baseIndexEquiv E6Data.base_cartan E6_cartan_connected
  | E7 =>
      change MatrixAdjacencyConnected E7Data.base.cartanMatrix
      exact matrixAdjacencyConnected_reindex (CartanMatrix.E 7) E7Data.base.cartanMatrix
        E7Data.baseIndexEquiv E7Data.base_cartan E7_cartan_connected
  | E8 =>
      change MatrixAdjacencyConnected E8Data.base.cartanMatrix
      exact matrixAdjacencyConnected_reindex (CartanMatrix.E 8) E8Data.base.cartanMatrix
        E8Data.baseIndexEquiv E8Data.base_cartan E8_cartan_connected
  | F4 =>
      change MatrixAdjacencyConnected F4Data.base.cartanMatrix
      exact matrixAdjacencyConnected_reindex (F4Table.cartan) F4Data.base.cartanMatrix
        F4Data.baseIndexEquiv F4Data.base_cartan F4_cartan_connected
  | G2 =>
      change MatrixAdjacencyConnected G2Data.base.cartanMatrix
      exact matrixAdjacencyConnected_reindex (G2Table.cartan) G2Data.base.cartanMatrix
        G2Data.baseIndexEquiv G2Data.base_cartan G2_cartan_connected

theorem rootDatum_cartan_closed_empty_or_univ (Φ : RootType)
    (J : Finset (rootDatum Φ).base.support)
    (hJ : ∀ i ∈ J, ∀ j, (rootDatum Φ).base.cartanMatrix i j ≠ 0 → j ∈ J) :
    J = ∅ ∨ J = Finset.univ := by
  rcases rootDatum_cartan_connected Φ (J : Set (rootDatum Φ).base.support) hJ with h | h
  · left
    exact Finset.coe_injective (by simpa using h)
  · right
    exact Finset.coe_injective (by simpa using h)

end Atlas.Chevalley

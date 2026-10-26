import Atlas.LinearGroups.Chevalley.Models
import Mathlib.Algebra.Ring.Int.Parity

/-! These are literal Cartan matrix row
conditions for already constructed bases. No group order or simplicity is used.
-/
namespace Atlas.Chevalley

private theorem E6_odd_rows : ∀ i : Fin 6, ∃ j : Fin 6,
    Odd (CartanMatrix.E 6 i j) := by
  intro i
  fin_cases i <;> decide
private theorem E7_odd_rows : ∀ i : Fin 7, ∃ j : Fin 7,
    Odd (CartanMatrix.E 7 i j) := by
  intro i
  fin_cases i <;> decide
private theorem E8_odd_rows : ∀ i : Fin 8, ∃ j : Fin 8,
    Odd (CartanMatrix.E 8 i j) := by
  intro i
  fin_cases i <;> decide
private theorem F4_odd_rows : ∀ i : Fin 4, ∃ j : Fin 4,
    Odd (F4Table.cartan i j) := by
  intro i
  fin_cases i <;> decide
private theorem G2_odd_rows : ∀ i : Fin 2, ∃ j : Fin 2,
    Odd (G2Table.cartan i j) := by
  intro i
  fin_cases i <;> decide

theorem E6_base_odd_rows : ∀ i : E6Data.base.support,
    ∃ j : E6Data.base.support, Odd (E6Data.base.cartanMatrix i j) := by
  intro i
  obtain ⟨k,rfl⟩ := E6Data.baseIndexEquiv.surjective i
  obtain ⟨l,hl⟩ := E6_odd_rows k
  exact ⟨E6Data.baseIndexEquiv l, by rwa [E6Data.base_cartan]⟩

theorem E7_base_odd_rows : ∀ i : E7Data.base.support,
    ∃ j : E7Data.base.support, Odd (E7Data.base.cartanMatrix i j) := by
  intro i
  obtain ⟨k,rfl⟩ := E7Data.baseIndexEquiv.surjective i
  obtain ⟨l,hl⟩ := E7_odd_rows k
  exact ⟨E7Data.baseIndexEquiv l, by rwa [E7Data.base_cartan]⟩

theorem E8_base_odd_rows : ∀ i : E8Data.base.support,
    ∃ j : E8Data.base.support, Odd (E8Data.base.cartanMatrix i j) := by
  intro i
  obtain ⟨k,rfl⟩ := E8Data.baseIndexEquiv.surjective i
  obtain ⟨l,hl⟩ := E8_odd_rows k
  exact ⟨E8Data.baseIndexEquiv l, by rwa [E8Data.base_cartan]⟩

theorem F4_base_odd_rows : ∀ i : F4Data.base.support,
    ∃ j : F4Data.base.support, Odd (F4Data.base.cartanMatrix i j) := by
  intro i
  obtain ⟨k,rfl⟩ := F4Data.baseIndexEquiv.surjective i
  obtain ⟨l,hl⟩ := F4_odd_rows k
  exact ⟨F4Data.baseIndexEquiv l, by rwa [F4Data.base_cartan]⟩

theorem G2_base_odd_rows : ∀ i : G2Data.base.support,
    ∃ j : G2Data.base.support, Odd (G2Data.base.cartanMatrix i j) := by
  intro i
  obtain ⟨k,rfl⟩ := G2Data.baseIndexEquiv.surjective i
  obtain ⟨l,hl⟩ := G2_odd_rows k
  exact ⟨G2Data.baseIndexEquiv l, by rwa [G2Data.base_cartan]⟩

end Atlas.Chevalley

/-! classical adjacency arithmetic. -/
namespace Atlas.Chevalley

theorem A_cartan_odd_rows (r : ℕ) (hr : 2 ≤ r) (i : Fin r) :
    ∃ j : Fin r, Odd (CartanMatrix.A r i j) := by
  suffices ∃ j : Fin r, CartanMatrix.A r i j = -1 by
    obtain ⟨j,hj⟩ := this
    exact ⟨j, by rw [hj]; decide⟩
  by_cases h0 : i.val = 0
  · refine ⟨⟨1,by omega⟩,?_⟩
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> omega
  · refine ⟨⟨i.val-1,by omega⟩,?_⟩
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> omega

theorem B_cartan_odd_rows (r : ℕ) (hr : 3 ≤ r) (i : Fin r) :
    ∃ j : Fin r, Odd (CartanMatrix.B r i j) := by
  suffices ∃ j : Fin r, CartanMatrix.B r i j = -1 by
    obtain ⟨j,hj⟩ := this
    exact ⟨j, by rw [hj]; decide⟩
  by_cases h0 : i.val = 0
  · refine ⟨⟨1,by omega⟩,?_⟩
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> omega
  · refine ⟨⟨i.val-1,by omega⟩,?_⟩
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> omega

theorem D_cartan_odd_rows (r : ℕ) (hr : 4 ≤ r) (i : Fin r) :
    ∃ j : Fin r, Odd (CartanMatrix.D r i j) := by
  suffices ∃ j : Fin r, CartanMatrix.D r i j = -1 by
    obtain ⟨j,hj⟩ := this
    exact ⟨j, by rw [hj]; decide⟩
  by_cases h0 : i.val = 0
  · refine ⟨⟨1,by omega⟩,?_⟩
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> omega
  · by_cases hbranch : r-2 ≤ i.val
    · refine ⟨⟨r-3,by omega⟩,?_⟩
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> omega
    · refine ⟨⟨i.val-1,by omega⟩,?_⟩
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> omega
end Atlas.Chevalley

/-! actual-base and actual-model application layer.
-/
namespace Atlas.Chevalley
open Group

theorem A_base_odd_rows (r : ℕ) (hr : 2 ≤ r) :
    ∀ i : (TypeAData.base r).support, ∃ j : (TypeAData.base r).support,
      Odd ((TypeAData.base r).cartanMatrix i j) := by
  intro i
  obtain ⟨k,rfl⟩ := (TypeAData.baseIndexEquiv r).surjective i
  obtain ⟨l,hl⟩ := A_cartan_odd_rows r hr k
  exact ⟨TypeAData.baseIndexEquiv r l, by rwa [TypeAData.base_cartan]⟩

theorem B_base_odd_rows (n : ℕ) (hn : 2 ≤ n) :
    ∀ i : (ClassicalData.baseB n).support, ∃ j : (ClassicalData.baseB n).support,
      Odd ((ClassicalData.baseB n).cartanMatrix i j) := by
  intro i
  obtain ⟨k,rfl⟩ := (ClassicalData.baseBIndexEquiv n).surjective i
  obtain ⟨l,hl⟩ := B_cartan_odd_rows (n+1) (by omega) k
  exact ⟨ClassicalData.baseBIndexEquiv n l, by rwa [ClassicalData.baseB_cartan]⟩

theorem D_base_odd_rows (n : ℕ) (hn : 2 ≤ n) :
    ∀ i : (ClassicalData.baseD n).support, ∃ j : (ClassicalData.baseD n).support,
      Odd ((ClassicalData.baseD n).cartanMatrix i j) := by
  intro i
  obtain ⟨k,rfl⟩ := (ClassicalData.baseDIndexEquiv n).surjective i
  obtain ⟨l,hl⟩ := D_cartan_odd_rows (n+2) (by omega) k
  exact ⟨ClassicalData.baseDIndexEquiv n l, by rwa [ClassicalData.baseD_cartan]⟩


end Atlas.Chevalley

import Atlas.OrderArithmetic.BinaryTables.F1
import Atlas.OrderArithmetic.BinaryTables.F2
import Atlas.OrderArithmetic.BinaryTables.F3
import Atlas.OrderArithmetic.BinaryTables.F4
import Atlas.OrderArithmetic.BinaryTables.F5
import Atlas.OrderArithmetic.BinaryTables.F6

import Mathlib.Tactic.IntervalCases

namespace Atlas.OrderArithmetic

set_option maxRecDepth 16384 in
theorem binaryClassicalBox_card : binaryClassicalBox.card = 182 := by decide +kernel

theorem binary_box_order_collision {x y : RawEntry}
    (hx : x ∈ binaryClassicalBox) (hy : y ∈ binaryClassicalBox)
    (he : order x = order y) : Collision x y := by
  obtain ⟨f, hf, hfx⟩ := Finset.mem_biUnion.mp hx
  have hf1 := (Finset.mem_Icc.mp hf).1
  have hf6 := (Finset.mem_Icc.mp hf).2
  apply binaryCollision_collision
  interval_cases f
  · exact binary_table_f1 x hfx y hy he
  · exact binary_table_f2 x hfx y hy he
  · exact binary_table_f3 x hfx y hy he
  · exact binary_table_f4 x hfx y hy he
  · exact binary_table_f5 x hfx y hy he
  · exact binary_table_f6 x hfx y hy he

theorem binary_index_bounded_collision {x y : RawEntry} {f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hcx : IsClassicalLie x) (hcy : IsClassicalLie y)
    (hf : 1 ≤ f) (hg : 1 ≤ g) (hqx : fieldSize x = 2 ^ f) (hqy : fieldSize y = 2 ^ g)
    (hbx : f * secondIndex x ≤ 6) (hby : g * secondIndex y ≤ 6)
    (he : order x = order y) : Collision x y := by
  obtain ⟨hf6, hrx⟩ := bounds_of_scaled_secondIndex_le_six hx hcx hf hbx
  obtain ⟨hg6, hry⟩ := bounds_of_scaled_secondIndex_le_six hy hcy hg hby
  exact binary_box_order_collision (mem_binaryClassicalBox hx hcx hf hf6 hqx hrx)
    (mem_binaryClassicalBox hy hcy hg hg6 hqy hry) he

theorem binary_top_bounded_collision {x y : RawEntry} {f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hcx : IsClassicalLie x) (hcy : IsClassicalLie y)
    (hf : 1 ≤ f) (hg : 1 ≤ g) (hqx : fieldSize x = 2 ^ f) (hqy : fieldSize y = 2 ^ g)
    (hbx : f * topIndex x ≤ 6) (hby : g * topIndex y ≤ 6)
    (he : order x = order y) : Collision x y := by
  obtain ⟨hf6, hrx⟩ := bounds_of_scaled_topIndex_le_six hx hcx hf hbx
  obtain ⟨hg6, hry⟩ := bounds_of_scaled_topIndex_le_six hy hcy hg hby
  exact binary_box_order_collision (mem_binaryClassicalBox hx hcx hf hf6 hqx hrx)
    (mem_binaryClassicalBox hy hcy hg hg6 hqy hry) he

end Atlas.OrderArithmetic

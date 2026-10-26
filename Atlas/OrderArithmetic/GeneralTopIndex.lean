import Atlas.OrderArithmetic.BinaryPrimitiveExistence
import Atlas.OrderArithmetic.OddTopIndex
import Atlas.OrderArithmetic.BinaryExceptionalBounds

namespace Atlas.OrderArithmetic

/-- Above the binary exceptional index, top-index comparison is unconditional. -/
theorem scaled_topIndex_le_of_equal_order_gt_six
    {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : 2 ≤ p) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) (hs : 6 < f * topIndex x) :
    f * topIndex x ≤ g * topIndex y := by
  obtain ⟨l, hl⟩ := primitiveDivisor_exists_of_index_gt_two hp (by omega : 2 < f * topIndex x)
    (by omega : ¬ (p = 2 ∧ f * topIndex x = 6))
  exact scaled_topIndex_le_of_equal_order_and_primitive hx hy hlx hly hp hf hg
    hqx hqy he (by omega) hl

/-- The sole remaining failure of automatic top equality lies in the finite
binary branch already checked separately. -/
theorem scaled_topIndex_eq_or_binary_small_of_equal_order
    {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : 2 ≤ p) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) :
    f * topIndex x = g * topIndex y ∨
      (p = 2 ∧ f * topIndex x ≤ 6 ∧ g * topIndex y ≤ 6) := by
  by_cases hp3 : 3 ≤ p
  · exact Or.inl (scaled_topIndex_eq_of_equal_order_base_ge_three hx hy hlx hly hp3
      hf hg hqx hqy he)
  have hp2 : p = 2 := by omega
  by_cases hsx : 6 < f * topIndex x
  · have hxy := scaled_topIndex_le_of_equal_order_gt_six hx hy hlx hly hp hf hg hqx hqy he hsx
    have hyx := scaled_topIndex_le_of_equal_order_gt_six hy hx hly hlx hp hg hf hqy hqx
      he.symm (by omega)
    exact Or.inl (Nat.le_antisymm hxy hyx)
  by_cases hsy : 6 < g * topIndex y
  · have hyx := scaled_topIndex_le_of_equal_order_gt_six hy hx hly hlx hp hg hf hqy hqx he.symm hsy
    omega
  · exact Or.inr ⟨hp2, by omega, by omega⟩

/-- Top-index equality or an already proved collision, in every characteristic. -/
theorem scaled_topIndex_eq_or_collision_of_equal_order
    {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : 2 ≤ p) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) : f * topIndex x = g * topIndex y ∨ Collision x y := by
  rcases scaled_topIndex_eq_or_binary_small_of_equal_order hx hy hlx hly hp hf hg hqx hqy he
    with ht | ⟨rfl, hbx, hby⟩
  · exact Or.inl ht
  · exact Or.inr (binary_lie_top_bounded_collision hx hy hlx hly hf hg hqx hqy hbx hby he)

end Atlas.OrderArithmetic

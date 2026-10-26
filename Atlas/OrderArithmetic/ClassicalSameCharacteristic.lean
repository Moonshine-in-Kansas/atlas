import Atlas.OrderArithmetic.GeneralTopIndex
import Atlas.OrderArithmetic.PrimitiveSecondOccurrence
import Atlas.OrderArithmetic.PrimitiveSecondGap
import Atlas.OrderArithmetic.ClassicalCollision

namespace Atlas.OrderArithmetic

/-- Second index one occurs only in linear dimension two. -/
theorem secondIndex_eq_one_linear_two {x : RawEntry} (hx : Admissible x)
    (hc : IsClassicalLie x) (hs : secondIndex x = 1) :
    ∃ q, x = .linear 2 q := by
  cases x with
  | linear d q =>
    have hd := hx.1
    simp only [secondIndex] at hs
    have he : d = 2 := by omega
    exact ⟨q, by rw [he]⟩
  | unitary d q =>
    have hd := hx.1
    simp only [secondIndex] at hs
    split_ifs at hs <;> omega
  | B r q | C r q | Dplus r q | Dminus r q =>
    simp only [secondIndex] at hs
    omega
  | _ => simp_all [IsClassicalLie]

/-- Scaled second index one forces scaled largest index two. -/
theorem scaled_top_eq_two_of_second_eq_one {x : RawEntry} {f : ℕ}
    (hx : Admissible x) (hc : IsClassicalLie x) (hf : 1 ≤ f)
    (hs : f * secondIndex x = 1) : f * topIndex x = 2 := by
  have hspos := secondIndex_one_le hx hc
  have hf1 : f = 1 := by nlinarith
  have hs1 : secondIndex x = 1 := by nlinarith
  obtain ⟨q, rfl⟩ := secondIndex_eq_one_linear_two hx hc hs1
  simp [hf1, topIndex]

/-- At common largest index two, the scaled second index is one. -/
theorem scaled_second_eq_one_of_top_eq_two {x : RawEntry} {f : ℕ}
    (hx : Admissible x) (hc : IsClassicalLie x) (hf : 1 ≤ f)
    (ht : f * topIndex x = 2) : f * secondIndex x = 1 := by
  have htop := topIndex_two_le hx (classical_isLie hc)
  have hf1 : f = 1 := by nlinarith
  have ht2 : topIndex x = 2 := by nlinarith
  obtain ⟨q, rfl⟩ := topIndex_eq_two_linear_two hx (classical_isLie hc) ht2
  simp [hf1, secondIndex]

/-- Unequal second indices at a common largest index cannot both be at most two. -/
theorem scaled_second_small_eq_of_common_top
    {x y : RawEntry} {f g : ℕ}
    (hx : Admissible x) (hy : Admissible y)
    (hcx : IsClassicalLie x) (hcy : IsClassicalLie y)
    (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hm : f * topIndex x = g * topIndex y)
    (hsx : f * secondIndex x ≤ 2) (hsy : g * secondIndex y ≤ 2) :
    f * secondIndex x = g * secondIndex y := by
  have hxp := secondIndex_one_le hx hcx
  have hyp := secondIndex_one_le hy hcy
  have hsxp : 1 ≤ f * secondIndex x := by nlinarith
  have hsyp : 1 ≤ g * secondIndex y := by nlinarith
  by_cases hx1 : f * secondIndex x = 1
  · have ht := scaled_top_eq_two_of_second_eq_one hx hcx hf hx1
    have hy1 := scaled_second_eq_one_of_top_eq_two hy hcy hg (by omega)
    omega
  by_cases hy1 : g * secondIndex y = 1
  · have ht := scaled_top_eq_two_of_second_eq_one hy hcy hg hy1
    have hx1 := scaled_second_eq_one_of_top_eq_two hx hcx hf (by omega)
    omega
  omega

/-- A supplied primitive divisor at the second index compares second indices
without any cancellation of cyclotomic values. -/
theorem scaled_second_le_of_equal_order_and_primitive
    {x y : RawEntry} {p f g l : ℕ}
    (hx : Admissible x) (hy : Admissible y)
    (hcx : IsClassicalLie x) (hcy : IsClassicalLie y)
    (hp : 2 ≤ p) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) (hm : f * topIndex x = g * topIndex y)
    (hs : 2 < f * secondIndex x)
    (hl : PrimitiveDivisor p (f * secondIndex x) l) :
    f * secondIndex x ≤ g * secondIndex y := by
  have hd := primitiveDivisor_second_dvd_order hx hcx hl hp hf hqx hs
  rw [he] at hd
  have hb := Nat.mul_lt_mul_of_pos_left (secondIndex_lt_topIndex hx hcx)
    (by omega : 0 < f)
  rw [hm] at hb
  exact primitiveDivisor_classical_order_second_gap hy hcy hl hp hg hqy hb hd

/-- Strict second-index inequality can survive equal orders and common top
only at the binary exponent-six primitive-divisor exception. -/
theorem unequal_second_forces_binary_six
    {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y)
    (hcx : IsClassicalLie x) (hcy : IsClassicalLie y)
    (hp : 2 ≤ p) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) (hm : f * topIndex x = g * topIndex y)
    (hs : g * secondIndex y < f * secondIndex x) :
    p = 2 ∧ f * secondIndex x = 6 := by
  have hs2 : 2 < f * secondIndex x := by
    by_contra hn
    have heq := scaled_second_small_eq_of_common_top hx hy hcx hcy hf hg hm
      (by omega) (by omega)
    omega
  by_contra hex
  obtain ⟨l, hl⟩ := primitiveDivisor_exists_of_index_gt_two hp hs2 hex
  have hb := scaled_second_le_of_equal_order_and_primitive hx hy hcx hcy hp hf hg
    hqx hqy he hm hs2 hl
  omega

/-- Common largest index gives common second index unless both labels lie in
the already bounded binary second-index range. -/
theorem scaled_second_eq_or_binary_small_of_common_top
    {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y)
    (hcx : IsClassicalLie x) (hcy : IsClassicalLie y)
    (hp : 2 ≤ p) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) (hm : f * topIndex x = g * topIndex y) :
    f * secondIndex x = g * secondIndex y ∨
      (p = 2 ∧ f * secondIndex x ≤ 6 ∧ g * secondIndex y ≤ 6) := by
  by_cases hs : f * secondIndex x = g * secondIndex y
  · exact Or.inl hs
  apply Or.inr
  rcases lt_or_gt_of_ne hs with hlt | hgt
  · obtain ⟨hp2, h6⟩ := unequal_second_forces_binary_six hy hx hcy hcx hp hg hf
      hqy hqx he.symm hm.symm hlt
    exact ⟨hp2, by omega, by omega⟩
  · obtain ⟨hp2, h6⟩ := unequal_second_forces_binary_six hx hy hcx hcy hp hf hg
      hqx hqy he hm hgt
    exact ⟨hp2, by omega, by omega⟩

/-- Uniform same-characteristic order-collision classification for admissible
classical labels, including characteristic two and every allowed field exponent. -/
theorem classical_same_characteristic_collision
    {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y)
    (hcx : IsClassicalLie x) (hcy : IsClassicalLie y)
    (hp : p.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) : Collision x y := by
  rcases scaled_topIndex_eq_or_collision_of_equal_order hx hy
    (classical_isLie hcx) (classical_isLie hcy) hp.two_le hf hg hqx hqy he with hm | hc
  · rcases scaled_second_eq_or_binary_small_of_common_top hx hy hcx hcy hp.two_le hf hg
      hqx hqy he hm with hs | ⟨rfl, hbx, hby⟩
    · exact classical_collision_of_scaled_indices hx hy hcx hcy hp hf hg hqx hqy he hm hs
    · exact binary_index_bounded_collision hx hy hcx hcy hf hg hqx hqy hbx hby he
  · exact hc

end Atlas.OrderArithmetic

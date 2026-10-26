import Atlas.OrderArithmetic.CyclotomicNoPrimitive
import Atlas.OrderArithmetic.PrimitiveIndexComparison
import Atlas.OrderArithmetic.ExponentReduction

namespace Atlas.OrderArithmetic

/-- Primitive-divisor existence removes the supplied-prime hypothesis from
top-index comparison for every base at least three. -/
theorem scaled_topIndex_le_of_equal_order_base_ge_three
    {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : 3 ≤ p) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) : f * topIndex x ≤ g * topIndex y := by
  by_cases hs : 2 < f * topIndex x
  · obtain ⟨l, hl⟩ := primitiveDivisor_exists_of_base_ge_three hp hs
    exact scaled_topIndex_le_of_equal_order_and_primitive hx hy hlx hly
      (by omega) hf hg hqx hqy he hs hl
  · have ht := topIndex_two_le hy hly
    nlinarith

/-- Equal numerical orders in a common odd characteristic have the same
scaled largest cyclotomic index. -/
theorem scaled_topIndex_eq_of_equal_order_base_ge_three
    {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : 3 ≤ p) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) : f * topIndex x = g * topIndex y := by
  exact Nat.le_antisymm
    (scaled_topIndex_le_of_equal_order_base_ge_three hx hy hlx hly hp hf hg hqx hqy he)
    (scaled_topIndex_le_of_equal_order_base_ge_three hy hx hly hlx hp hg hf hqy hqx he.symm)

/-- The finite exceptional template reduction needs no assumed ratio in odd
characteristic: equality of orders forces the ratio. -/
theorem exponent_top_ratio_of_equal_order_odd_characteristic
    {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) :
    characteristicExponent x * topIndex y = characteristicExponent y * topIndex x := by
  have hv := equal_order_exponents hx hy hlx hly hp hf hg hqx hqy he
  have ht := scaled_topIndex_eq_of_equal_order_base_ge_three hx hy hlx hly hp3 hf hg hqx hqy he
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < f)
  calc
    f * (characteristicExponent x * topIndex y) =
        (f * characteristicExponent x) * topIndex y := by ring
    _ = (g * characteristicExponent y) * topIndex y := by rw [hv]
    _ = characteristicExponent y * (g * topIndex y) := by ring
    _ = characteristicExponent y * (f * topIndex x) := by rw [← ht]
    _ = f * (characteristicExponent y * topIndex x) := by ring

end Atlas.OrderArithmetic

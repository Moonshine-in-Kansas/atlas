import Atlas.OrderArithmetic.ClassicalSameCharacteristic
import Atlas.OrderArithmetic.ExceptionalOddCollision

namespace Atlas.OrderArithmetic

theorem lie_classical_or_exceptional {x : RawEntry} (hx : IsLie x) :
    IsClassicalLie x ∨ IsExceptionalLie x := by
  cases x <;> simp_all [IsLie, IsClassicalLie, IsExceptionalLie]

/-- Complete numerical collision classification within a common characteristic.
No bound on the ranks, prime, or field exponents is imposed. -/
theorem same_characteristic_collision {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : p.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) : Collision x y := by
  have hExceptional (hex : IsExceptionalLie x ∨ IsExceptionalLie y) : Collision x y := by
    rcases scaled_topIndex_eq_or_collision_of_equal_order hx hy hlx hly hp.two_le hf hg hqx hqy he
      with ht | hc
    · have hv := equal_order_exponents hx hy hlx hly hp hf hg hqx hqy he
      have hr : characteristicExponent x * topIndex y =
          characteristicExponent y * topIndex x := by
        apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < f)
        calc
          f * (characteristicExponent x * topIndex y) =
              (f * characteristicExponent x) * topIndex y := by ring
          _ = (g * characteristicExponent y) * topIndex y := by rw [hv]
          _ = characteristicExponent y * (g * topIndex y) := by ring
          _ = characteristicExponent y * (f * topIndex x) := by rw [← ht]
          _ = f * (characteristicExponent y * topIndex x) := by ring
      have hxy := exceptional_eq_of_equal_order_and_ratio hx hy hlx hly hex hp hf hg hqx hqy he hr
      subst y
      exact Or.inl rfl
    · exact hc
  rcases lie_classical_or_exceptional hlx with hcx | hex
  · rcases lie_classical_or_exceptional hly with hcy | hey
    · exact classical_same_characteristic_collision hx hy hcx hcy hp hf hg hqx hqy he
    · exact hExceptional (Or.inr hey)
  · exact hExceptional (Or.inl hex)

end Atlas.OrderArithmetic

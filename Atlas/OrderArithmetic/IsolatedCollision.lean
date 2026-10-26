import Atlas.OrderArithmetic.FiniteTables

namespace Atlas.OrderArithmetic

/-- The small unitary exceptions already have exhaustive integer-order tables. -/
theorem unitary_three_three_equal_order_collision {y : RawEntry}
    (hy : Admissible y) (hly : IsLie y)
    (he : order (.unitary 3 3) = order y) : Collision (.unitary 3 3) y := by
  have hy' := (order_eq_6048_iff hy hly).mp (he.symm.trans regression_6048)
  subst y
  exact Or.inl rfl

theorem unitary_four_two_equal_order_collision {y : RawEntry}
    (hy : Admissible y) (hly : IsLie y)
    (he : order (.unitary 4 2) = order y) : Collision (.unitary 4 2) y := by
  have hy' := (order_eq_25920_iff hy hly).mp (he.symm.trans order_unitary_4_2)
  rcases hy' with rfl | rfl | rfl <;> apply Or.inl <;> norm_num [normalize]

end Atlas.OrderArithmetic

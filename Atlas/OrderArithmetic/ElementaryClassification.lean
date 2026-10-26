import Atlas.OrderArithmetic.FixedTables
import Atlas.OrderArithmetic.AlternatingTables
import Atlas.OrderArithmetic.Cyclic

namespace Atlas.OrderArithmetic

theorem exceptional_symm {x y : RawEntry} (h : Exceptional x y) : Exceptional y x := by
  rcases h with h | h | ⟨r, q, hr, hq, ho, h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨r, q, hr, hq, ho, h.symm⟩)

theorem collision_symm {x y : RawEntry} (h : Collision x y) : Collision y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (exceptional_symm h)

/-- Each fixed constant is isolated from every other admissible catalogue label. -/
theorem fixed_order_eq_iff {x : RawEntry} (hx : Admissible x) (s : FixedLabel) :
    order x = order (.fixed s) ↔ x = .fixed s := by
  constructor
  · intro h
    cases x with
    | fixed t => exact congrArg RawEntry.fixed (fixedOrder_injective h)
    | cyclic p => exact False.elim (cyclic_ne_fixed hx s h)
    | alternating n => exact False.elim (alternating_ne_fixed hx s h)
    | _ => exact False.elim (lie_ne_fixed hx trivial s h)
  · rintro rfl
    rfl

theorem prime_order_eq_iff {x : RawEntry} {p : ℕ} (hx : Admissible x) (hp : p.Prime) :
    order x = p ↔ x = .cyclic p := by
  constructor
  · intro h
    cases x with
    | cyclic q => exact congrArg RawEntry.cyclic h
    | alternating n => exact False.elim (alternating_not_prime hx (h.symm ▸ hp))
    | fixed s =>
      apply False.elim
      apply fixedOrder_not_prime s
      change (order (.fixed s)).Prime
      rw [h]
      exact hp
    | _ => exact False.elim (lie_order_not_prime hx trivial (h.symm ▸ hp))
  · rintro rfl
    rfl

/-- The complete equality classification when at least one label is not of Lie type. -/
theorem catalogue_order_eq_iff_elementary {x y : RawEntry}
    (hx : Admissible x) (hy : Admissible y) (he : ¬ IsLie x ∨ ¬ IsLie y) :
    order x = order y ↔ Collision x y := by
  have left_case : ∀ {u v : RawEntry}, Admissible u → Admissible v → ¬ IsLie u →
      order u = order v → Collision u v := by
    intro u v hu hv hn h
    cases u with
    | cyclic p =>
      have heq := (prime_order_eq_iff hv hu).mp h.symm
      subst v
      exact Or.inl rfl
    | fixed s =>
      have heq := (fixed_order_eq_iff hv s).mp h.symm
      subst v
      exact Or.inl rfl
    | alternating n =>
      cases v with
      | cyclic p => exact False.elim (cyclic_ne_alternating hv hu h.symm)
      | fixed s => exact False.elim (alternating_ne_fixed hu s h)
      | alternating m =>
        have heq := alternating_order_injective hu hv h
        subst m
        exact Or.inl rfl
      | _ => exact collision_symm (alternating_lie_collision hv trivial hu h.symm)
    | _ => exact False.elim (hn trivial)
  constructor
  · intro h
    rcases he with he | he
    · exact left_case hx hy he h
    · exact collision_symm (left_case hy hx he h.symm)
  · exact collision_order

end Atlas.OrderArithmetic

import Atlas.Tits.Order
import Atlas.GroupTheory.IndexTwoNonsquareSimplicity
import Atlas.Tits.OrderArithmetic
import Mathlib.GroupTheory.IsPerfect

/-! Simplicity of the actual derived cross stabilizer. The order was established
 independently through transfer. Nonsquare order rules out a proper normal
 subgroup paired with its conjugate under the ambient index-two extension. -/
namespace Atlas.Tits

/-- Nonabelian simplicity of the actual derived subgroup model. -/
theorem isSimpleGroup : IsSimpleGroup Model := by
  letI : Nontrivial Model := Finite.one_lt_card_iff_nontrivial.mp (by rw [card]; decide)
  apply Atlas.GroupTheory.simple_of_index_two_minimal_normal_nonsquare derivedSubgroup
    index_derived
  · exact ambient_normal_contains_derived
  · intro n
    rw [show Nat.card derivedSubgroup = 17971200 from card]
    exact derived_order_not_square n

theorem nonabelian : ¬IsMulCommutative Model := by
  intro h
  letI := isSimpleGroup
  letI : CommGroup Model :=
    Group.commGroupOfCenterEqTop (Subgroup.center_eq_top_iff.mpr h)
  have hp := IsSimpleGroup.prime_card (α := Model)
  rw [card] at hp
  have hd : 2 ∣ 17971200 := ⟨8985600,rfl⟩
  have he := (Nat.dvd_prime hp).mp hd
  norm_num at he

theorem noncommutative : ∃a b : Model, a*b ≠ b*a := by
  classical
  simpa only [isMulCommutative_iff,not_forall] using nonabelian

/-- Perfectness is a consequence of verified simplicity and noncommutativity. -/
theorem perfect : Group.IsPerfect Model := by
  letI := isSimpleGroup
  constructor
  rcases (inferInstance : (commutator Model).Normal).eq_bot_or_eq_top with h | h
  · exact False.elim (nonabelian ((commutator_eq_bot_iff Model).mp h))
  · exact h

end Atlas.Tits

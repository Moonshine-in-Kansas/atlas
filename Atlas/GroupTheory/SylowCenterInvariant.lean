import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Subgroup.Center

/-! The center cardinality of a Sylow subgroup is a group-isomorphism invariant. -/
noncomputable section
namespace Atlas.GroupTheory
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
variable {p : ℕ} [Fact p.Prime]

/-- Transport followed by Sylow conjugacy compares the actual subgroup carriers. -/
def sylowEquivOfMulEquiv (e : G ≃* H) (P : Sylow p G) (Q : Sylow p H) : P ≃* Q :=
  (e.subgroupMap P.toSubgroup).trans ((P.mapSurjective e.surjective).equiv Q)

/-- The corresponding actual centers, not merely their cardinalities. -/
def sylowCenterEquiv (e : G ≃* H) (P : Sylow p G) (Q : Sylow p H) :
    Subgroup.center P ≃* Subgroup.center Q :=
  Subgroup.centerCongr (sylowEquivOfMulEquiv e P Q)

theorem sylow_center_card_eq_of_mulEquiv (e : G ≃* H)
    (P : Sylow p G) (Q : Sylow p H) :
    Nat.card (Subgroup.center P) = Nat.card (Subgroup.center Q) :=
  Nat.card_congr (sylowCenterEquiv e P Q).toEquiv

theorem not_mulEquiv_of_sylow_center_card_ne (P : Sylow p G) (Q : Sylow p H)
    (h : Nat.card (Subgroup.center P) ≠ Nat.card (Subgroup.center Q)) :
    ¬ Nonempty (G ≃* H) := by
  rintro ⟨e⟩
  exact h (sylow_center_card_eq_of_mulEquiv e P Q)

end Atlas.GroupTheory

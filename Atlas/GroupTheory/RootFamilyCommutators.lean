import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Commute.Hom

/-! Pointwise commutator formulas imply subgroup-range containments. -/
namespace Atlas.GroupTheory
open scoped commutatorElement

theorem rootRange_commutator_le {R G : Type*} [CommRing R] [Group G]
    (x y : Multiplicative R →* G) (K : Subgroup G)
    (h : ∀ s t : R, ⁅x (Multiplicative.ofAdd s), y (Multiplicative.ofAdd t)⁆ ∈ K) :
    ⁅x.range, y.range⁆ ≤ K := by
  apply Subgroup.commutator_le.mpr
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
  exact h s.toAdd t.toAdd

theorem rootRange_commutator_le_of_commute {R G : Type*} [CommRing R] [Group G]
    (x y : Multiplicative R →* G) (K : Subgroup G)
    (h : ∀ s t : R, Commute (x (Multiplicative.ofAdd s)) (y (Multiplicative.ofAdd t))) :
    ⁅x.range, y.range⁆ ≤ K := by
  apply rootRange_commutator_le x y K
  intro s t
  rw [(h s t).commutator_eq]
  exact K.one_mem

theorem rootRange_self_commutator_le {R G : Type*} [CommRing R] [Group G]
    (x : Multiplicative R →* G) (K : Subgroup G) : ⁅x.range, x.range⁆ ≤ K :=
  rootRange_commutator_le_of_commute x x K fun s t => Commute.map (Commute.all _ _) x

end Atlas.GroupTheory

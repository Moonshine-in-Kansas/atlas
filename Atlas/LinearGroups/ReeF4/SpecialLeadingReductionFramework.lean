import Atlas.LinearGroups.ReeF4.SpecialLeadingExistence
import Atlas.LinearGroups.ReeF4.ElementaryDerived

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def SpecialLeadingAt (r : Fin 26) (u : TraceZero F) : Prop :=
  isotropyCoordinates u r≠0 ∧
    ∀ j, specialAbsoluteGrade r<specialAbsoluteGrade j → isotropyCoordinates u j=0

/-- The established eight-root theorem upgrades a bound on allowed coordinates
into a bound on every coordinate, including both marked diagonal coefficients. -/
theorem IsSpecialVector.support_bound_of_allowed {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) {u : TraceZero F} (hu : IsSpecialVector m u)
    (r : Fin 26)
    (hb : ∀ j, allowedSpecialLeadingRoot j → specialAbsoluteGrade r<specialAbsoluteGrade j →
      isotropyCoordinates u j=0) :
    ∀ j, specialAbsoluteGrade r<specialAbsoluteGrade j → isotropyCoordinates u j=0 := by
  obtain ⟨s,hs,hn,hz⟩ := hu.exists_allowed_leading_root hcard
  have hsr : specialAbsoluteGrade s≤specialAbsoluteGrade r := by
    by_contra h
    exact hn (hb s hs (lt_of_not_ge h))
  intro j hj
  exact hz j (lt_of_le_of_lt hsr hj)

/-- A concrete elementary word carries a vector to the retained lowest root.
This property is stronger than orbit membership for the full intrinsic model. -/
def ElementaryReducesToLowest {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F) : Prop :=
  ∃ g : Model F m, g∈elementarySubgroup hcard ∧ g.val u=rootVector (0,0)

theorem elementaryReducesToLowest_of_map {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) {u : TraceZero F} (g : Model F m)
    (hg : g∈elementarySubgroup hcard)
    (hr : ElementaryReducesToLowest hcard (g.val u)) : ElementaryReducesToLowest hcard u := by
  obtain ⟨k,hk,he⟩ := hr
  refine ⟨k*g,(elementarySubgroup hcard).mul_mem hk hg,?_⟩
  exact he
end Atlas.ReeF4

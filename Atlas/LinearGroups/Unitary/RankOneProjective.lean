import Atlas.LinearGroups.Unitary.RankOne
import Atlas.LinearGroups.PSLFamily

/-! Projective rank-one comparison and its exact simplicity exceptions.
The comparison is induced by the explicit special-group isomorphism. -/
noncomputable section
namespace Atlas.Unitary
open scoped MatrixGroups
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Quotienting the actual special-group comparison by its actual full centers. -/
def projectiveUnitaryTwoEquiv (hdeg : Module.finrank F K = 2) :
    PSL(2,F) ≃* PSU F K 2 hdeg :=
  QuotientGroup.congr _ _ (specialUnitaryTwoEquiv hdeg)
    (Subgroup.map_center_eq (specialUnitaryTwoEquiv hdeg))

/-- Exact dimension-two simplicity range, transported through an actual equivalence. -/
theorem psu_two_simple_iff (hdeg : Module.finrank F K = 2) :
    IsSimpleGroup (PSU F K 2 hdeg) ↔ Nat.card F ≠ 2 ∧ Nat.card F ≠ 3 := by
  have he := projectiveUnitaryTwoEquiv hdeg
  constructor
  · intro h
    let := h
    have hs : IsSimpleGroup PSL(2,F) := he.isSimpleGroup
    simpa using (Atlas.psl_simple_iff (F := F) 2 (by decide)).mp hs
  · intro h
    have hs : IsSimpleGroup PSL(2,F) :=
      (Atlas.psl_simple_iff (F := F) 2 (by decide)).mpr (by simpa using h)
    let := hs
    exact he.symm.isSimpleGroup

/-- Noncommutativity holds in every positive rank-one simplicity case. -/
theorem psu_two_noncommutative (hdeg : Module.finrank F K = 2)
    (hq : 4 ≤ Nat.card F) : ¬ IsMulCommutative (PSU F K 2 hdeg) := by
  intro h
  apply Atlas.psl_nonabelian_rank_two (F := F) hq
  apply IsMulCommutative.of_comm
  intro x y
  apply (projectiveUnitaryTwoEquiv hdeg).injective
  simp only [map_mul]
  exact isMulCommutative_iff.mp h _ _

theorem psu_two_binary_not_simple (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) : ¬ IsSimpleGroup (PSU F K 2 hdeg) := by
  rw [psu_two_simple_iff hdeg, hq]
  simp

theorem psu_two_ternary_not_simple (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 3) : ¬ IsSimpleGroup (PSU F K 2 hdeg) := by
  rw [psu_two_simple_iff hdeg, hq]
  simp
end Atlas.Unitary

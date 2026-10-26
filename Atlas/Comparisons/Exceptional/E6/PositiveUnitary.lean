import Atlas.Comparisons.Exceptional.E6.BinarySign
import Atlas.LinearGroups.Orthogonal.Minus.RankThreeComparison
import Atlas.LinearGroups.Orthogonal.ProjectiveEvenB
import Atlas.LinearGroups.Unitary.Family
import Atlas.LinearGroups.Unitary.ProjectiveOrder
import Atlas.LinearGroups.Unitary.OrderChecks

/-! The positive integral Weyl group is the actual PSU4(2) model.
Simplicity is transferred from the independently verified unitary construction. -/
noncomputable section
namespace Atlas.Comparisons.E6Lattice
open Atlas.Orthogonal
variable {K : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K]
variable (hdeg : Module.finrank (ZMod 2) K = 2)

def positiveWeylUnitaryEquiv : positiveWeyl ≃* Atlas.Unitary.PSU (ZMod 2) K 4 hdeg :=
  (positiveWeylMinusEquiv hdeg).trans
    ((evenProjectiveElementaryEquiv (Minus.form hdeg 2)).symm.trans
      (Minus.rankThreeUnitaryEquiv hdeg).symm)

theorem positiveWeyl_simple : IsSimpleGroup positiveWeyl := by
  let h := Atlas.Unitary.OrderChecks.binary_degree
  letI := Atlas.Unitary.simple_of_good h
    (show Atlas.Unitary.Good 4 (Nat.card (ZMod 2)) by simp [Atlas.Unitary.Good])
  exact (positiveWeylUnitaryEquiv h).isSimpleGroup

theorem positiveWeyl_card : Nat.card positiveWeyl = 25920 := by
  rw [Nat.card_congr (positiveWeylUnitaryEquiv Atlas.Unitary.OrderChecks.binary_degree).toEquiv,
    Atlas.Unitary.card_psu _ 4 (by decide)]
  norm_num [Atlas.Unitary.orderSU,Atlas.Unitary.orderFactor,Finset.prod_range_succ,Nat.card_zmod]

end Atlas.Comparisons.E6Lattice

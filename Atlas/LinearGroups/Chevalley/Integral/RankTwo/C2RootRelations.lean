import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2WeylCorrespondence
import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2UniversalRelations
import Mathlib.GroupTheory.Commutator.Basic

/-! Actual C2 commutators. The faithful map is a reindexing of the
existing adjoint group. No new permutation model or recognition is involved. -/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo
open ClassicalData
open scoped commutatorElement
local instance c2RelationsRootDecidableEq : DecidableEq (BRoot 2) := Classical.decEq _
local instance c2RelationsBaseDecidableEq : DecidableEq (baseC 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseC 1).support})
variable {R : Type*} [CommRing R]

/-- The signed relation for the two short positive roots of actual C2. -/
theorem c2_short_short_product (s t : R) :
    adjointX (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 0) s * c2Z t =
      c2W (-2*s*t) * c2Z t *
        adjointX (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 0) s := by
  apply c2AdjointMatrixHom_injective R
  simp only [map_mul, c2_matrix_xshort, c2_matrix_Z, c2_matrix_W]
  exact C2UniversalRelations.same_root_relation s t

/-- The mixed relation has Z before W with the fixed integral pinning. -/
theorem c2_short_long_product (s t : R) :
    adjointX (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 0) s *
      adjointX (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 1) t =
      c2Z (-s*t) * c2W (s^2*t) *
        adjointX (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 1) t *
        adjointX (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 0) s := by
  apply c2AdjointMatrixHom_injective R
  simp only [map_mul, c2_matrix_xshort, c2_matrix_xlong, c2_matrix_Z, c2_matrix_W]
  exact C2UniversalRelations.mixed_root_relation s t

private theorem commutator_of_product {G : Type*} [Group G] (x y z : G)
    (h : x*y = z*y*x) : ⁅x,y⁆ = z := by
  rw [commutatorElement_def, h]
  group

/-- The coefficient -2 is integral, so the identity also holds in characteristic2. -/
theorem c2_short_short_commutator (s t : R) :
    ⁅adjointX (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 0) s, c2Z t⁆ =
      c2W (-2*s*t) :=
  commutator_of_product _ _ _ (c2_short_short_product s t)

theorem c2_short_long_commutator (s t : R) :
    ⁅adjointX (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 0) s,
      adjointX (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 1) t⁆ =
      c2Z (-s*t) * c2W (s^2*t) :=
  commutator_of_product _ _ _ (c2_short_long_product s t)

end Atlas.Chevalley.Integral.RankTwo

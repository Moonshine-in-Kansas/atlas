import Atlas.LinearGroups.Chevalley.Integral.UnimodularWeightLattice
import Atlas.LinearGroups.Chevalley.RootData.E8
import Atlas.LinearGroups.Chevalley.RootData.SmallExceptional

/-! Actual root/weight lattice equality for E8, F4 and G2. -/
noncomputable section
namespace Atlas.Chevalley
open Integral.Minuscule

/-- No additional minuscule weight summand is needed for the E8 weight lattice. -/
theorem E8Data.rootLattice_eq_top : rootLattice E8Data.pairing = ⊤ := by
  apply rootLattice_eq_top_of_cartan_isUnit_det E8Data.pairing E8Data.base
    E8Data.baseIndexEquiv (CartanMatrix.E 8) E8Data.base_cartan
  rw [CartanMatrix.E₈_det]
  exact isUnit_one

/-- No additional minuscule weight summand is needed for the F4 weight lattice. -/
theorem F4Data.rootLattice_eq_top : rootLattice F4Data.pairing = ⊤ := by
  apply rootLattice_eq_top_of_cartan_isUnit_det F4Data.pairing F4Data.base
    F4Data.baseIndexEquiv F4Table.cartan F4Data.base_cartan
  rw [F4Table.cartan, CartanMatrix.F₄_det]
  exact isUnit_one

/-- No additional minuscule weight summand is needed for the G2 weight lattice. -/
theorem G2Data.rootLattice_eq_top : rootLattice G2Data.pairing = ⊤ := by
  apply rootLattice_eq_top_of_cartan_isUnit_det G2Data.pairing G2Data.base
    G2Data.baseIndexEquiv G2Table.cartan G2Data.base_cartan
  rw [G2Table.cartan, CartanMatrix.G₂_det]
  exact isUnit_one

end Atlas.Chevalley

import Atlas.Codes.TernaryGolayAutomorphisms

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Codes
open scoped BigOperators

/-- It suffices to check the six marked generators for a coordinate permutation. -/
theorem ternaryCoordinatePreserves_of_basis (g : Equiv.Perm (Fin 12))
    (hg : ∀ j : Fin 6,(fun i => ternaryEncoder (Pi.single j 1) (g.symm i)) ∈ ternaryGolay) :
    TernaryCoordinatePreserves g := by
  rintro w ⟨p,rfl⟩
  let L := (LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) g.symm).toLinearMap
  have hp : (∑ j : Fin 6,p j • (Pi.single j 1 : TernaryParameters))=p := by
    ext i
    simp [Finset.sum_apply,Pi.single_apply]
  change L (ternaryEncoder p) ∈ ternaryGolay
  rw [← hp,map_sum,map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [map_smul,map_smul]
  exact Submodule.smul_mem _ _ (hg j)

end Atlas.Codes

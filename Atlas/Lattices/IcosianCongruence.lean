import Atlas.Algebra.IcosianRightIdeals
import Atlas.Algebra.IcosianModuloTwoCoordinates
import Atlas.Lattices.IcosianRationalSpace

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators

abbrev IcosianCoordinates := Fin 3 → icosianOrder

/-- The specified rank-three right-icosian congruence module. -/
def icosianLeechModule : Submodule icosianOrderᵐᵒᵖ IcosianCoordinates where
  carrier := {x | x 1-x 0 ∈ icosianP ∧ x 2-x 0 ∈ icosianP ∧
    x 0+x 1+x 2 ∈ icosianPZero}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨h1,h2,h0⟩ ⟨k1,k2,k0⟩
    refine ⟨?_,?_,?_⟩
    · convert icosianP.add_mem h1 k1 using 1 <;> simp [Pi.add_apply] <;> abel
    · convert icosianP.add_mem h2 k2 using 1 <;> simp [Pi.add_apply] <;> abel
    · convert icosianPZero.add_mem h0 k0 using 1 <;> simp [Pi.add_apply] <;> abel
  smul_mem' := by
    rintro c x ⟨h1,h2,h0⟩
    exact ⟨by simpa [smul_sub] using icosianP.smul_mem c h1,
      by simpa [smul_sub] using icosianP.smul_mem c h2,
      by simpa [smul_add] using icosianPZero.smul_mem c h0⟩

theorem icosianLeechModule_mem (x : IcosianCoordinates) :
    x ∈ icosianLeechModule ↔ x 1-x 0 ∈ icosianP ∧ x 2-x 0 ∈ icosianP ∧
      x 0+x 1+x 2 ∈ icosianPZero := Iff.rfl

def icosianCoordinateEmbedding : IcosianCoordinates →ₗ[ℤ] IcosianRationalCoordinates where
  toFun x i := (x i).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rationalIcosianLattice : Submodule ℤ IcosianRationalCoordinates :=
  (icosianLeechModule.restrictScalars ℤ).map icosianCoordinateEmbedding

theorem rationalIcosianLattice_mem (z : IcosianRationalCoordinates) :
    z ∈ rationalIcosianLattice ↔ ∃ x : IcosianCoordinates,
      x ∈ icosianLeechModule ∧ icosianCoordinateEmbedding x=z := Iff.rfl

end Atlas.Lattices

import Atlas.Lattices.IcosianComparisonLattice
import Atlas.Lattices.LeechFullIsometries
import Atlas.Lattices.LeechRank

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra

abbrev IcosianLattice := icosianLeechModule

theorem icosianCoordinateEmbedding_injective : Function.Injective icosianCoordinateEmbedding := by
  intro x y h
  funext i
  exact Subtype.ext (congrFun h i)

def icosianIntegralEmbeddingEquiv : IcosianLattice ≃ₗ[ℤ] rationalIcosianLattice :=
  Submodule.equivMapOfInjective icosianCoordinateEmbedding
    icosianCoordinateEmbedding_injective (icosianLeechModule.restrictScalars ℤ)

def icosianRationalLatticeEquiv : rationalIcosianLattice ≃ₗ[ℤ] rationalLeech where
  toFun z := ⟨icosianComparison z.val, icosianComparison_forward z.val z.property⟩
  invFun x := ⟨icosianComparison.symm x.val, icosianComparison_reverse x.val x.property⟩
  left_inv z := Subtype.ext (icosianComparison.symm_apply_apply z.val)
  right_inv x := Subtype.ext (icosianComparison.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add icosianComparison x.val y.val)
  map_smul' r z := Subtype.ext (map_zsmul icosianComparison r z.val)

/-- The integral linear equivalence onto the retained Golay Leech lattice. -/
def icosianLeechEquiv : IcosianLattice ≃ₗ[ℤ] leech :=
  icosianIntegralEmbeddingEquiv.trans (icosianRationalLatticeEquiv.trans latticeEmbeddingEquiv.symm)

theorem icosianLeechEquiv_agrees (z : IcosianLattice) :
    rationalEmbedding (icosianLeechEquiv z).val =
      icosianComparison (icosianCoordinateEmbedding z.val) := by
  have h := latticeEmbeddingEquiv.apply_symm_apply (icosianRationalLatticeEquiv
    (icosianIntegralEmbeddingEquiv z))
  exact congrArg Subtype.val h

theorem icosianLeechEquiv_isometry (x y : IcosianLattice) :
    rationalForm (rationalEmbedding (icosianLeechEquiv x).val)
      (rationalEmbedding (icosianLeechEquiv y).val) =
    icosianBilinear (icosianCoordinateEmbedding x.val) (icosianCoordinateEmbedding y.val) := by
  rw [icosianLeechEquiv_agrees,icosianLeechEquiv_agrees,icosianComparison_isometry]

instance icosianLeech_free : Module.Free ℤ IcosianLattice :=
  Module.Free.of_equiv icosianLeechEquiv.symm

instance icosianLeech_finite : Module.Finite ℤ IcosianLattice :=
  Module.Finite.equiv icosianLeechEquiv.symm

theorem icosianLeech_rank : Module.finrank ℤ IcosianLattice = 24 := by
  rw [icosianLeechEquiv.finrank_eq]
  exact leech_rank

end Atlas.Lattices

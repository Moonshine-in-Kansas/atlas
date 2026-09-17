import Atlas.Conway.IcosianMonomialAction
import Atlas.Conway.IcosianCentralizer

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

def icosianMonomialToHermitian : icosianLiftedMonomial →* icosianHermitianGroup where
  toFun g := ⟨icosianMonomialRepresentation g.val,
    icosianMonomialRepresentation_right_linear g.val,
    icosianMonomialRepresentation_hermitian g.val,fun x => by
      constructor
      · exact icosianLiftedMonomial_lattice g x
      · intro hx
        have h := icosianLiftedMonomial_lattice g⁻¹ _ hx
        simpa only [Subgroup.coe_inv,map_inv,LinearEquiv.coe_inv,
          LinearEquiv.symm_apply_apply] using h⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

end Atlas.Conway

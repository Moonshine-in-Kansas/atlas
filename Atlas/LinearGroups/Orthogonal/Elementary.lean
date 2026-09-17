import Atlas.LinearGroups.Orthogonal.Basic
import Atlas.LinearAlgebra.QuadraticSiegel

/-! # The actual elementary Siegel subgroup of a quadratic isometry group -/
noncomputable section
namespace Atlas.Orthogonal
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

def siegelElement (u v : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) : isometrySubgroup Q :=
  (isometryCarrierEquiv Q).symm (Atlas.Quadratic.siegelIsometry Q u v hu huv)

def elementarySubgroup : Subgroup (isometrySubgroup Q) :=
  Subgroup.closure {g | ∃ u v hu huv, g = siegelElement Q u v hu huv}

theorem siegelElement_mem (u v : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    siegelElement Q u v hu huv ∈ elementarySubgroup Q :=
  Subgroup.subset_closure ⟨u, v, hu, huv, rfl⟩

end Atlas.Orthogonal

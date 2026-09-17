import Atlas.LinearGroups.Orthogonal.Elementary
import Atlas.LinearAlgebra.QuadraticSiegelDeterminant

/-! # The actual determinant kernel and its elementary subgroup -/
noncomputable section
namespace Atlas.Orthogonal
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

def determinant : isometrySubgroup Q →* Fˣ :=
  LinearEquiv.det.comp (isometrySubgroup Q).subtype

/-- The determinant-one kernel. This is not the intrinsic Omega kernel. -/
def specialSubgroup : Subgroup (isometrySubgroup Q) := (determinant Q).ker

@[simp] theorem mem_specialSubgroup (g : isometrySubgroup Q) :
    g ∈ specialSubgroup Q ↔ g.val.det = 1 := Iff.rfl

theorem siegelElement_determinant (u v : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    determinant Q (siegelElement Q u v hu huv) = 1 :=
  Atlas.Quadratic.siegelIsometry_det Q u v hu huv

theorem elementary_le_special : elementarySubgroup Q ≤ specialSubgroup Q := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, v, hu, huv, rfl⟩
  exact siegelElement_determinant Q u v hu huv

end Atlas.Orthogonal

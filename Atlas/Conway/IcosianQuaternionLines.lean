import Atlas.Conway.IcosianCentralizer
import Atlas.Algebra.IcosianDivision
import Mathlib.LinearAlgebra.Projectivization.Action

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped Pointwise

/-- Right quaternionic lines, using mathlib projectivization over the opposite division ring. -/
abbrev IcosianQuaternionPoint := Projectivization IcosianQuaternionᵐᵒᵖ IcosianRationalCoordinates

instance icosianHermitian_comm_right_scalars :
    SMulCommClass icosianHermitianGroup IcosianQuaternionᵐᵒᵖ IcosianRationalCoordinates where
  smul_comm g a x := g.property.1 (MulOpposite.unop a) x

/-- The coordinate quaternionic line, not a chosen root representative. -/
def icosianAxisPoint (i : Fin 3) : IcosianQuaternionPoint :=
  Projectivization.mk _ (Pi.single i (1 : IcosianQuaternion)) (by
    intro h
    have hi := congrFun h i
    simpa using hi)

theorem icosianAxisPoint_injective : Function.Injective icosianAxisPoint := by
  intro i j h
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mp h
  by_contra hij
  have hi := congrFun ha i
  simpa [Pi.single_apply,hij] using hi

def icosianCoordinateFrame : Set IcosianQuaternionPoint := Set.range icosianAxisPoint

def icosianCoordinateFrameStabilizer : Subgroup icosianHermitianGroup :=
  MulAction.stabilizer icosianHermitianGroup icosianCoordinateFrame

end Atlas.Conway

import Atlas.Conway.IcosianRootLocalReferences
import Atlas.Algebra.IcosianIntegralCheck

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes

/-- Explicit reduction of the candidate recovered from the rational basis
coordinates; no choice of integral coefficients occurs in this expression. -/
def icosianCandidateMatrix (x : IcosianQuaternion) : IcosianMatrix :=
  icosianMatrixFromCoefficients (fun i => goldenModuloTwo
    (goldenNumerator (icosianBasisCoefficients x i)))

theorem icosianCandidateMatrix_eq (x : IcosianQuaternion) :
    icosianCandidateMatrix x=icosianModuloTwo (icosianIntegralCandidate x) :=
  (icosianModuloTwo_synthesis _).symm

def icosianLocalCConjugate (u : IcosianQuaternion) : IcosianQuaternion :=
  (1/2 : ℚ) • (icosianLocalCScalar.val*u*star icosianLocalCScalar.val)

def IcosianLocalCScalarTest (v : IcosianIntegerCoordinates) : Prop :=
  let u := icosianCoordinatesQuaternion v
  let z := icosianLocalCConjugate u
  let a := icosianCandidateMatrix u
  let b := icosianCandidateMatrix z
  IcosianIntegralTest z ∧ a 1 0=0 ∧
    b 0 0=a 0 0 ∧ b 1 1=a 1 1 ∧ b 1 0=0 ∧ b 0 1=0

instance (v : IcosianIntegerCoordinates) : Decidable (IcosianLocalCScalarTest v) :=
  inferInstanceAs (Decidable (let u := icosianCoordinatesQuaternion v
    let z := icosianLocalCConjugate u
    let a := icosianCandidateMatrix u
    let b := icosianCandidateMatrix z
    IcosianIntegralTest z ∧ a 1 0=0 ∧
      b 0 0=a 0 0 ∧ b 1 1=a 1 1 ∧ b 1 0=0 ∧ b 0 1=0))

def icosianLocalCScalarCandidates : Finset IcosianIntegerCoordinates :=
  icosianNormOneCoordinates.filter IcosianLocalCScalarTest

/-- The bounded scalar calculation concerns only the actual120 integral units,
not an ambient root or permutation representation. -/
theorem icosianLocalCScalarCandidates_card : icosianLocalCScalarCandidates.card=6 := by
  decide +kernel

end Atlas.Conway

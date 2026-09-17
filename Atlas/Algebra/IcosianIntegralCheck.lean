import Atlas.Algebra.IcosianIntegralCoordinates
import Mathlib.Data.Rat.Defs

noncomputable section
namespace Atlas.Algebra

def goldenNumerator (a : GoldenRational) : GoldenInteger := ⟨a.re.num,a.im.num⟩

@[simp] theorem goldenNumerator_integer (a : GoldenInteger) :
    goldenNumerator (goldenIntegerToRational a)=a := by
  ext <;> simp [goldenNumerator,goldenIntegerToRational]

/-- A computable candidate integral quaternion, equal to the input exactly when
its four golden coefficients are integral. -/
def icosianIntegralCandidate (x : IcosianQuaternion) : icosianOrder :=
  icosianIntegralSynthesis (fun i => goldenNumerator (icosianBasisCoefficients x i))

attribute [local irreducible] icosianBasisSynthesis icosianBasisCoefficients goldenIntegerToRational

theorem icosianIntegralCandidate_eq (x : IcosianQuaternion) (hx : IsIcosian x) :
    (icosianIntegralCandidate x).val=x := by
  change icosianBasisSynthesis _=x
  have h : (fun i => goldenIntegerToRational (goldenNumerator (icosianBasisCoefficients x i)))=
      icosianBasisCoefficients x := by
    funext i
    obtain ⟨a,ha⟩ := hx i
    rw [← ha,goldenNumerator_integer]
  rw [h,icosianBasisSynthesis_coefficients]

theorem isIcosian_iff_candidate (x : IcosianQuaternion) :
    IsIcosian x ↔ (icosianIntegralCandidate x).val=x :=
  ⟨icosianIntegralCandidate_eq x,fun h => h ▸ (icosianIntegralCandidate x).property⟩

/-- A finite coefficient test for integrality, suitable for kernel reduction. -/
def IcosianIntegralTest (x : IcosianQuaternion) : Prop :=
  ∀ i : Fin 4,goldenIntegerToRational (goldenNumerator (icosianBasisCoefficients x i))=
    icosianBasisCoefficients x i

instance (x : IcosianQuaternion) : Decidable (IcosianIntegralTest x) :=
  inferInstanceAs (Decidable (∀ i : Fin 4,
    goldenIntegerToRational (goldenNumerator (icosianBasisCoefficients x i))=
      icosianBasisCoefficients x i))

theorem isIcosian_iff_integralTest (x : IcosianQuaternion) : IsIcosian x ↔ IcosianIntegralTest x := by
  constructor
  · intro hx i
    obtain ⟨a,ha⟩ := hx i
    rw [← ha,goldenNumerator_integer]
  · intro h i
    exact ⟨goldenNumerator (icosianBasisCoefficients x i),h i⟩

end Atlas.Algebra

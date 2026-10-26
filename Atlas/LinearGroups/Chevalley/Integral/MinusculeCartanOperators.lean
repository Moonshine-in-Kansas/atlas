import Atlas.LinearGroups.Chevalley.Integral.MinusculeOpposite

/-! Actual local operator identities supporting further steps toward the actual Lie-module bridge.
No central-kernel conclusion or equivariant map is assumed. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.Strings
variable {I Ω : Type*} (S : Strings I Ω) (R : Type*) [CommRing R]

/-- Literal integral weight grades, reduced to the coefficient ring. -/
def gradeOperator (i : I) : Module.End R (OrbitModule (Ω := Ω) R) :=
  Finsupp.linearCombination R fun μ => Finsupp.single μ (S.pairing i μ : R)

@[simp] theorem gradeOperator_single (i : I) (μ : Ω) (r : R) :
    S.gradeOperator R i (Finsupp.single μ r) =
      Finsupp.single μ ((S.pairing i μ : R)*r) := by
  classical
  simp [gradeOperator, mul_comm]

/-- The actual rank-one Cartan operator is the E/F commutator, including
characteristics two and three; this is not a representation assumption. -/
theorem raising_lowering_sub (i : I) :
    S.raising R i * S.lowering R i - S.lowering R i * S.raising R i =
      S.gradeOperator R i := by
  apply Finsupp.lhom_ext
  intro μ r
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  rcases S.minuscule i μ with h | h | h
  all_goals
    simp [raising, lowering, step_single, h, S.pairing_reflection,
      S.involutive i μ, gradeOperator_single]
end Atlas.Chevalley.Integral.Minuscule.Strings

namespace Atlas.Chevalley.Integral.Minuscule
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]
  (S : Finset (WeightLattice P))
  (hc : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
  (hm : ∀ μ, μ ∈ S → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

/-- Actual H_j/E_i or H_j/F_i relation on the literal weight module.
For epsilon=-1 this has coefficient Cartan(i,j), for epsilon=1 its negative. -/
theorem weightOrbit_grade_step_sub (i j : ι) (ε : ℤ) :
    let T := stringsOfWeightOrbit P S hc hm
    T.gradeOperator R j * T.step R i ε - T.step R i ε * T.gradeOperator R j =
      ((-ε * P.pairingIn ℤ i j : ℤ) : R) • T.step R i ε := by
  let T := stringsOfWeightOrbit P S hc hm
  change T.gradeOperator R j * T.step R i ε - T.step R i ε * T.gradeOperator R j =
    ((-ε * P.pairingIn ℤ i j : ℤ) : R) • T.step R i ε
  apply Finsupp.lhom_ext
  intro μ r
  have hg : T.pairing j (T.reflection i μ) =
      T.pairing j μ - T.pairing i μ * P.pairingIn ℤ i j :=
    weightReflection_other_grade P j i μ.val
  by_cases h : T.pairing i μ = ε
  · simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Strings.step_single, Strings.gradeOperator_single, h, if_pos, hg,
      Finsupp.smul_single, smul_eq_mul]
    rw [← Finsupp.single_sub]
    congr 1
    push_cast
    ring
  · simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Strings.step_single, Strings.gradeOperator_single, h, if_neg, ite_false, map_zero, sub_self, smul_zero]

/-- H_j E_i - E_i H_j, with the actual root/coroot orientation. -/
theorem weightOrbit_grade_raising_sub (i j : ι) :
    let T := stringsOfWeightOrbit P S hc hm
    T.gradeOperator R j * T.raising R i - T.raising R i * T.gradeOperator R j =
      (P.pairingIn ℤ i j : R) • T.raising R i := by
  simpa only [Strings.raising, neg_neg, one_mul] using
    weightOrbit_grade_step_sub P S hc hm R i j (-1)

/-- H_j F_i - F_i H_j, valid in every coefficient characteristic. -/
theorem weightOrbit_grade_lowering_sub (i j : ι) :
    let T := stringsOfWeightOrbit P S hc hm
    T.gradeOperator R j * T.lowering R i - T.lowering R i * T.gradeOperator R j =
      (-P.pairingIn ℤ i j : R) • T.lowering R i := by
  simpa only [Strings.lowering, neg_one_mul, Int.cast_neg] using
    weightOrbit_grade_step_sub P S hc hm R i j 1

end Atlas.Chevalley.Integral.Minuscule

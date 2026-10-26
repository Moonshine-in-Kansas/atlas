import Atlas.LinearGroups.Chevalley.Integral.MinusculeStrings
import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeightLattice

/-! Rank-one Weyl words and diagonal torus action over every commutative ring.
The grade-zero Weyl formula fixes the original basis vector: generic Strings
permits its supplied reflection to move grade-zero indices. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.Strings
variable {I Ω : Type*} (S : Strings I Ω) (R : Type*) [CommRing R]

def weylEquiv (i : I) (t : Rˣ) : OrbitModule (Ω := Ω) R ≃ₗ[R] OrbitModule (Ω := Ω) R :=
  S.rootEquiv R i (-1) (by decide) t.val *
    S.rootEquiv R i 1 (by decide) (-t.inv) *
      S.rootEquiv R i (-1) (by decide) t.val

theorem weylEquiv_single_neg (i : I) (t : Rˣ) (μ : Ω) (r : R)
    (h : S.pairing i μ = -1) :
    S.weylEquiv R i t (Finsupp.single μ r) =
      Finsupp.single (S.reflection i μ) (t.val * r) := by
  have hr : S.pairing i (S.reflection i μ) = 1 := by rw [S.pairing_reflection, h]; decide
  simp [weylEquiv, rootEquiv, transvection_apply, step_single, h, hr,
    S.involutive i μ, map_add, Finsupp.smul_single, smul_eq_mul, mul_assoc]

theorem weylEquiv_single_pos (i : I) (t : Rˣ) (μ : Ω) (r : R)
    (h : S.pairing i μ = 1) :
    S.weylEquiv R i t (Finsupp.single μ r) =
      Finsupp.single (S.reflection i μ) (-t.inv * r) := by
  have hr : S.pairing i (S.reflection i μ) = -1 := by rw [S.pairing_reflection, h]
  simp [weylEquiv, rootEquiv, transvection_apply, step_single, h, hr,
    S.involutive i μ, map_add, Finsupp.smul_single, smul_eq_mul, mul_assoc]

/-- This conclusion deliberately does not mention reflection of a grade-zero index. -/
theorem weylEquiv_single_zero (i : I) (t : Rˣ) (μ : Ω) (r : R)
    (h : S.pairing i μ = 0) :
    S.weylEquiv R i t (Finsupp.single μ r) = Finsupp.single μ r := by
  simp [weylEquiv, rootEquiv, transvection_apply, step_single, h]

def torusEquiv (i : I) (t : Rˣ) : OrbitModule (Ω := Ω) R ≃ₗ[R] OrbitModule (Ω := Ω) R :=
  S.weylEquiv R i t * (S.weylEquiv R i 1)⁻¹

/-- The inverse at one is computed using the proved Weyl formulas and actual
involutivity; no hypothesis about the grade-zero permutation is needed. -/
theorem inverse_weyl_one_single (i : I) (μ : Ω) (r : R) :
    (S.weylEquiv R i 1)⁻¹ (Finsupp.single μ r) =
      if S.pairing i μ = -1 then Finsupp.single (S.reflection i μ) (-r)
      else if S.pairing i μ = 1 then Finsupp.single (S.reflection i μ) r
      else Finsupp.single μ r := by
  apply (S.weylEquiv R i 1).injective
  rcases S.minuscule i μ with h | h | h
  · have hr : S.pairing i (S.reflection i μ) = 1 := by rw [S.pairing_reflection, h]; decide
    simp [h, S.weylEquiv_single_pos R i 1 _ _ hr, S.involutive i μ]
  · simp [h, S.weylEquiv_single_zero R i 1 μ r h]
  · have hr : S.pairing i (S.reflection i μ) = -1 := by rw [S.pairing_reflection, h]
    simp [h, S.weylEquiv_single_neg R i 1 _ _ hr, S.involutive i μ]

/-- Unit powers of integral grades make this valid over every commutative ring. -/
theorem torusEquiv_single (i : I) (t : Rˣ) (μ : Ω) (r : R) :
    S.torusEquiv R i t (Finsupp.single μ r) =
      Finsupp.single μ ((t ^ S.pairing i μ).val * r) := by
  change S.weylEquiv R i t ((S.weylEquiv R i 1)⁻¹ (Finsupp.single μ r)) = _
  rw [S.inverse_weyl_one_single]
  rcases S.minuscule i μ with h | h | h
  · have hr : S.pairing i (S.reflection i μ) = 1 := by rw [S.pairing_reflection, h]; decide
    simp [h, S.weylEquiv_single_pos R i t _ _ hr, S.involutive i μ]
  · simp [h, S.weylEquiv_single_zero R i t μ r h]
  · have hr : S.pairing i (S.reflection i μ) = -1 := by rw [S.pairing_reflection, h]
    simp [h, S.weylEquiv_single_neg R i t _ _ hr, S.involutive i μ]

variable [Fintype Ω] [DecidableEq Ω]

def weylMatrix (i : I) (t : Rˣ) : Matrix Ω Ω R :=
  LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
    (S.weylEquiv R i t).toLinearMap

theorem weylMatrix_word (i : I) (t : Rˣ) :
    S.weylMatrix R i t = S.rootMatrix R i (-1) t.val *
      S.rootMatrix R i 1 (-t.inv) * S.rootMatrix R i (-1) t.val := by
  simp only [weylMatrix, weylEquiv, LinearEquiv.coe_toLinearMap_mul,
    LinearMap.toMatrix_mul, rootMatrix_eq_toMatrix, rootEquiv, LinearEquiv.toLinearMap_ofLinearMap]

def torusMatrix (i : I) (t : Rˣ) : Matrix Ω Ω R :=
  LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
    (S.torusEquiv R i t).toLinearMap

theorem torusMatrix_diagonal (i : I) (t : Rˣ) :
    S.torusMatrix R i t = Matrix.diagonal (fun μ => (t ^ S.pairing i μ).val) := by
  ext μ ν
  rw [torusMatrix, LinearMap.toMatrix_apply]
  change S.torusEquiv R i t (Finsupp.single ν 1) μ = _
  rw [S.torusEquiv_single]
  by_cases h : μ = ν <;> simp [h]

end Atlas.Chevalley.Integral.Minuscule.Strings

namespace Atlas.Chevalley.Integral.Minuscule
variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (P : RootPairing ι ℤ M N)

/-- Unlike abstract Strings, actual weight reflections fix every grade-zero weight. -/
theorem weightReflection_fixed_of_zero (i : ι) (μ : WeightLattice P)
    (h : μ (corootElement P i) = 0) : weightReflection P i μ = μ := by
  rw [weightReflection_apply, h, zero_smul, sub_zero]

end Atlas.Chevalley.Integral.Minuscule

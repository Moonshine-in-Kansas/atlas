import Atlas.LinearGroups.Triality.PositiveCoordinates

/-! Expanded action of the ordered positive product, verified from its root definitions. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def positiveAction (a : K) (b : F) (c d : K) (u v : F) (x : VectorD 4 K) : VectorD 4 K :=
  Sum.elim ![
    (1) * x (.inl 0) + (a) * x (.inl 1) + (-(c) + a * (algebraMap F K b)) * x (.inl 2) + ((FiniteCubic.sigma F K (FiniteCubic.sigma F K d)) + a * (FiniteCubic.sigma F K c)) * x (.inl 3) + (-(a * (algebraMap F K v)) + c * (algebraMap F K u) + -((FiniteCubic.sigma F K d) * (FiniteCubic.sigma F K (FiniteCubic.sigma F K d))) + -(a * (algebraMap F K b) * (algebraMap F K u)) + -(a * (FiniteCubic.sigma F K c) * (FiniteCubic.sigma F K d)) + -(a * (FiniteCubic.sigma F K (FiniteCubic.sigma F K c)) * (FiniteCubic.sigma F K (FiniteCubic.sigma F K d)))) * x (.inr 0) + ((algebraMap F K v) + c * d + -(a * (algebraMap F K b) * d) + -(a * (FiniteCubic.sigma F K c) * (FiniteCubic.sigma F K (FiniteCubic.sigma F K c)))) * x (.inr 1) + ((algebraMap F K u) + a * d) * x (.inr 2) + ((FiniteCubic.sigma F K d) + a * (FiniteCubic.sigma F K (FiniteCubic.sigma F K c))) * x (.inr 3),
    (1) * x (.inl 1) + ((algebraMap F K b)) * x (.inl 2) + ((FiniteCubic.sigma F K c)) * x (.inl 3) + (-((algebraMap F K v)) + -((algebraMap F K b) * (algebraMap F K u)) + -((FiniteCubic.sigma F K c) * (FiniteCubic.sigma F K d)) + -((FiniteCubic.sigma F K (FiniteCubic.sigma F K c)) * (FiniteCubic.sigma F K (FiniteCubic.sigma F K d)))) * x (.inr 0) + (-((algebraMap F K b) * d) + -((FiniteCubic.sigma F K c) * (FiniteCubic.sigma F K (FiniteCubic.sigma F K c)))) * x (.inr 1) + (d) * x (.inr 2) + ((FiniteCubic.sigma F K (FiniteCubic.sigma F K c))) * x (.inr 3),
    (1) * x (.inl 2) + ((FiniteCubic.sigma F K a)) * x (.inl 3) + (-((algebraMap F K u)) + -((FiniteCubic.sigma F K a) * (FiniteCubic.sigma F K d)) + -((FiniteCubic.sigma F K (FiniteCubic.sigma F K a)) * (FiniteCubic.sigma F K (FiniteCubic.sigma F K d))) + -((FiniteCubic.sigma F K a) * (FiniteCubic.sigma F K (FiniteCubic.sigma F K a)) * c)) * x (.inr 0) + (-(d) + -((FiniteCubic.sigma F K a) * (FiniteCubic.sigma F K (FiniteCubic.sigma F K c))) + -((FiniteCubic.sigma F K (FiniteCubic.sigma F K a)) * (FiniteCubic.sigma F K c)) + (FiniteCubic.sigma F K a) * (FiniteCubic.sigma F K (FiniteCubic.sigma F K a)) * (algebraMap F K b)) * x (.inr 1) + (-((FiniteCubic.sigma F K a) * (FiniteCubic.sigma F K (FiniteCubic.sigma F K a)))) * x (.inr 2) + ((FiniteCubic.sigma F K (FiniteCubic.sigma F K a))) * x (.inr 3),
    (1) * x (.inl 3) + (-((FiniteCubic.sigma F K d)) + -((FiniteCubic.sigma F K (FiniteCubic.sigma F K a)) * c)) * x (.inr 0) + (-((FiniteCubic.sigma F K (FiniteCubic.sigma F K c))) + (FiniteCubic.sigma F K (FiniteCubic.sigma F K a)) * (algebraMap F K b)) * x (.inr 1) + (-((FiniteCubic.sigma F K (FiniteCubic.sigma F K a)))) * x (.inr 2)]
    ![(1) * x (.inr 0),
    (-(a)) * x (.inr 0) + (1) * x (.inr 1),
    (c) * x (.inr 0) + (-((algebraMap F K b))) * x (.inr 1) + (1) * x (.inr 2),
    (-((FiniteCubic.sigma F K (FiniteCubic.sigma F K d))) + -((FiniteCubic.sigma F K a) * c)) * x (.inr 0) + (-((FiniteCubic.sigma F K c)) + (FiniteCubic.sigma F K a) * (algebraMap F K b)) * x (.inr 1) + (-((FiniteCubic.sigma F K a))) * x (.inr 2) + (1) * x (.inr 3)]

set_option maxHeartbeats 6000000 in
-- Expand the eight fixed coordinates once, for reuse in collection identities.
theorem positiveWord_apply (a : K) (b : F) (c d : K) (u v : F) (x : VectorD 4 K) :
    (positiveWord F K a b c d u v).val x = positiveAction F K a b c d u v x := by
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [positiveAction, positiveWord, shortRoot, longRoot, nextShortRoot, middleRoot,
      highLongRoot, highestRoot, pinnedRoot, Subgroup.coe_mul, LinearEquiv.mul_apply,
      differenceRoot_apply, sumRoot_apply, e, f, Algebra.smul_def] <;> ring

end Atlas.Triality

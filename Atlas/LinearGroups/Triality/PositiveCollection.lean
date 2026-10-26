import Atlas.LinearGroups.Triality.PositiveAction

/-! Exact collection law for the six relative positive-root parameters. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal

structure PositiveParameters (F K : Type*) where
  a : K
  b : F
  c : K
  d : K
  u : F
  v : F

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def positiveMatrix (p : PositiveParameters F K) : O_DPlus 4 K :=
  positiveWord F K p.a p.b p.c p.d p.u p.v

/-- The collection coefficients use actual trace and norm, so the long-root
parameters remain in the base field, also in characteristics two and three. -/
def positiveCollect (p r : PositiveParameters F K) : PositiveParameters F K where
  a := p.a+r.a
  b := p.b+r.b
  c := p.c+r.c+r.a*algebraMap F K p.b
  d := p.d+r.d - FiniteCubic.sigma F K r.a * FiniteCubic.sigma F K (FiniteCubic.sigma F K p.c) -
    FiniteCubic.sigma F K (FiniteCubic.sigma F K r.a) * FiniteCubic.sigma F K p.c -
    FiniteCubic.sigma F K r.a * FiniteCubic.sigma F K (FiniteCubic.sigma F K r.a) * algebraMap F K p.b
  u := p.u+r.u - FiniteCubic.trace F K (r.a*p.d) +
    FiniteCubic.trace F K (r.a * FiniteCubic.sigma F K r.a *
      FiniteCubic.sigma F K (FiniteCubic.sigma F K p.c)) + FiniteCubic.norm F K r.a*p.b
  v := p.v+r.v-r.b*p.u - FiniteCubic.trace F K (r.c*p.d) +
    r.b * FiniteCubic.trace F K (r.a*p.d) +
    FiniteCubic.trace F K
      (r.a * FiniteCubic.sigma F K r.c * FiniteCubic.sigma F K (FiniteCubic.sigma F K p.c) +
       r.a * FiniteCubic.sigma F K (FiniteCubic.sigma F K r.c) * FiniteCubic.sigma F K p.c +
       r.a * FiniteCubic.sigma F K p.c * FiniteCubic.sigma F K (FiniteCubic.sigma F K p.c)) +
    (p.b-r.b) * FiniteCubic.trace F K (r.a * FiniteCubic.sigma F K r.a *
      FiniteCubic.sigma F K (FiniteCubic.sigma F K p.c)) +
    p.b * FiniteCubic.trace F K (r.a * FiniteCubic.sigma F K r.a *
      FiniteCubic.sigma F K (FiniteCubic.sigma F K r.c)) +
    FiniteCubic.norm F K r.a * p.b * (p.b-r.b)

set_option maxHeartbeats 12000000 in
-- The fixed eight-coordinate multiplication identity is checked by polynomial normalization.
theorem positiveMatrix_mul (hdeg : Module.finrank F K = 3) (p r : PositiveParameters F K) :
    positiveMatrix F K p * positiveMatrix F K r = positiveMatrix F K (positiveCollect F K p r) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (positiveWord F K p.a p.b p.c p.d p.u p.v).val
    ((positiveWord F K r.a r.b r.c r.d r.u r.v).val x) =
    (positiveWord F K _ _ _ _ _ _).val x
  simp only [positiveWord_apply]
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [positiveCollect, positiveAction, FiniteCubic.trace_formula hdeg,
      FiniteCubic.norm_formula hdeg, FiniteCubic.sigma_cube hdeg, Algebra.smul_def] <;> ring

end Atlas.Triality

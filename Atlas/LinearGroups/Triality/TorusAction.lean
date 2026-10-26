import Atlas.LinearGroups.Triality.TorusRankOne
import Atlas.LinearGroups.Triality.Unipotent

/-! The explicit torus action on the positive-root coordinates. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def normUnit : Kˣ →* Fˣ := Units.map (FiniteCubic.norm F K)

theorem base_normUnit (hdeg : Module.finrank F K = 3) (a : Kˣ) :
    baseUnit F K (normUnit F K a) = a * sigmaUnit F K a * sigmaUnit F K (sigmaUnit F K a) := by
  apply Units.ext
  exact FiniteCubic.norm_formula hdeg a

def torusScale (h : Kˣ × Fˣ) (p : PositiveParameters F K) : PositiveParameters F K where
  a := ((h.1^2 / baseUnit F K h.2 : Kˣ) : K) * p.a
  b := ((h.2^2 / normUnit F K h.1 : Fˣ) : F) * p.b
  c := ((h.1 * baseUnit F K h.2 / (sigmaUnit F K h.1 * sigmaUnit F K (sigmaUnit F K h.1)) : Kˣ) : K) * p.c
  d := ((sigmaUnit F K h.1 * sigmaUnit F K (sigmaUnit F K h.1) / h.1 : Kˣ) : K) * p.d
  u := ((normUnit F K h.1 / h.2 : Fˣ) : F) * p.u
  v := (h.2 : F) * p.v

set_option maxHeartbeats 2500000 in
-- Check one relative root before composing the six conjugation identities.
theorem torus_shortRoot_intertwine (hdeg : Module.finrank F K = 3)
    (h : Kˣ × Fˣ) (p : PositiveParameters F K) :
    torusMap F K h * shortRoot F K p.a =
      shortRoot F K (torusScale F K h p).a * torusMap F K h := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (torusMap F K h).val ((shortRoot F K p.a).val x) =
    (shortRoot F K (torusScale F K h p).a).val ((torusMap F K h).val x)
  have ha : (h.1 : K) ≠ 0 := h.1.ne_zero
  have hb : algebraMap F K (h.2 : F) ≠ 0 := (baseUnit F K h.2).ne_zero
  have ha1 : FiniteCubic.sigma F K (h.1 : K) ≠ 0 := (sigmaUnit F K h.1).ne_zero
  have ha2 : FiniteCubic.sigma F K (FiniteCubic.sigma F K (h.1 : K)) ≠ 0 := (sigmaUnit F K (sigmaUnit F K h.1)).ne_zero
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [torusMap, torusWeights, diagonalEmbedding, diagonalLinear,
      torusScale, sigmaUnit, baseUnit, normUnit, FiniteCubic.norm_formula hdeg,
      FiniteCubic.sigma_cube hdeg, Algebra.smul_def, shortRoot, pinnedRoot,
      Subgroup.coe_mul, LinearEquiv.mul_apply, differenceRoot_apply, sumRoot_apply, e, f] <;>
    field_simp <;> ring

set_option maxHeartbeats 2500000 in
-- Check one relative root before composing the six conjugation identities.
theorem torus_longRoot_intertwine (hdeg : Module.finrank F K = 3)
    (h : Kˣ × Fˣ) (p : PositiveParameters F K) :
    torusMap F K h * longRoot F K p.b =
      longRoot F K (torusScale F K h p).b * torusMap F K h := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (torusMap F K h).val ((longRoot F K p.b).val x) =
    (longRoot F K (torusScale F K h p).b).val ((torusMap F K h).val x)
  have ha : (h.1 : K) ≠ 0 := h.1.ne_zero
  have hb : algebraMap F K (h.2 : F) ≠ 0 := (baseUnit F K h.2).ne_zero
  have ha1 : FiniteCubic.sigma F K (h.1 : K) ≠ 0 := (sigmaUnit F K h.1).ne_zero
  have ha2 : FiniteCubic.sigma F K (FiniteCubic.sigma F K (h.1 : K)) ≠ 0 := (sigmaUnit F K (sigmaUnit F K h.1)).ne_zero
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [torusMap, torusWeights, diagonalEmbedding, diagonalLinear,
      torusScale, sigmaUnit, baseUnit, normUnit, FiniteCubic.norm_formula hdeg,
      FiniteCubic.sigma_cube hdeg, Algebra.smul_def, longRoot, pinnedRoot,
      Subgroup.coe_mul, LinearEquiv.mul_apply, differenceRoot_apply, sumRoot_apply, e, f] <;>
    field_simp <;> ring

set_option maxHeartbeats 2500000 in
-- Check one relative root before composing the six conjugation identities.
theorem torus_nextShortRoot_intertwine (hdeg : Module.finrank F K = 3)
    (h : Kˣ × Fˣ) (p : PositiveParameters F K) :
    torusMap F K h * nextShortRoot F K p.c =
      nextShortRoot F K (torusScale F K h p).c * torusMap F K h := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (torusMap F K h).val ((nextShortRoot F K p.c).val x) =
    (nextShortRoot F K (torusScale F K h p).c).val ((torusMap F K h).val x)
  have ha : (h.1 : K) ≠ 0 := h.1.ne_zero
  have hb : algebraMap F K (h.2 : F) ≠ 0 := (baseUnit F K h.2).ne_zero
  have ha1 : FiniteCubic.sigma F K (h.1 : K) ≠ 0 := (sigmaUnit F K h.1).ne_zero
  have ha2 : FiniteCubic.sigma F K (FiniteCubic.sigma F K (h.1 : K)) ≠ 0 := (sigmaUnit F K (sigmaUnit F K h.1)).ne_zero
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [torusMap, torusWeights, diagonalEmbedding, diagonalLinear,
      torusScale, sigmaUnit, baseUnit, normUnit, FiniteCubic.norm_formula hdeg,
      FiniteCubic.sigma_cube hdeg, Algebra.smul_def, nextShortRoot, pinnedRoot,
      Subgroup.coe_mul, LinearEquiv.mul_apply, differenceRoot_apply, sumRoot_apply, e, f] <;>
    field_simp <;> ring

set_option maxHeartbeats 2500000 in
-- Check one relative root before composing the six conjugation identities.
theorem torus_middleRoot_intertwine (hdeg : Module.finrank F K = 3)
    (h : Kˣ × Fˣ) (p : PositiveParameters F K) :
    torusMap F K h * middleRoot F K p.d =
      middleRoot F K (torusScale F K h p).d * torusMap F K h := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (torusMap F K h).val ((middleRoot F K p.d).val x) =
    (middleRoot F K (torusScale F K h p).d).val ((torusMap F K h).val x)
  have ha : (h.1 : K) ≠ 0 := h.1.ne_zero
  have hb : algebraMap F K (h.2 : F) ≠ 0 := (baseUnit F K h.2).ne_zero
  have ha1 : FiniteCubic.sigma F K (h.1 : K) ≠ 0 := (sigmaUnit F K h.1).ne_zero
  have ha2 : FiniteCubic.sigma F K (FiniteCubic.sigma F K (h.1 : K)) ≠ 0 := (sigmaUnit F K (sigmaUnit F K h.1)).ne_zero
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [torusMap, torusWeights, diagonalEmbedding, diagonalLinear,
      torusScale, sigmaUnit, baseUnit, normUnit, FiniteCubic.norm_formula hdeg,
      FiniteCubic.sigma_cube hdeg, Algebra.smul_def, middleRoot, pinnedRoot,
      Subgroup.coe_mul, LinearEquiv.mul_apply, differenceRoot_apply, sumRoot_apply, e, f] <;>
    field_simp <;> ring

set_option maxHeartbeats 2500000 in
-- Check one relative root before composing the six conjugation identities.
theorem torus_highLongRoot_intertwine (hdeg : Module.finrank F K = 3)
    (h : Kˣ × Fˣ) (p : PositiveParameters F K) :
    torusMap F K h * highLongRoot F K p.u =
      highLongRoot F K (torusScale F K h p).u * torusMap F K h := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (torusMap F K h).val ((highLongRoot F K p.u).val x) =
    (highLongRoot F K (torusScale F K h p).u).val ((torusMap F K h).val x)
  have ha : (h.1 : K) ≠ 0 := h.1.ne_zero
  have hb : algebraMap F K (h.2 : F) ≠ 0 := (baseUnit F K h.2).ne_zero
  have ha1 : FiniteCubic.sigma F K (h.1 : K) ≠ 0 := (sigmaUnit F K h.1).ne_zero
  have ha2 : FiniteCubic.sigma F K (FiniteCubic.sigma F K (h.1 : K)) ≠ 0 := (sigmaUnit F K (sigmaUnit F K h.1)).ne_zero
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [torusMap, torusWeights, diagonalEmbedding, diagonalLinear,
      torusScale, sigmaUnit, baseUnit, normUnit, FiniteCubic.norm_formula hdeg,
      FiniteCubic.sigma_cube hdeg, Algebra.smul_def, highLongRoot, pinnedRoot,
      Subgroup.coe_mul, LinearEquiv.mul_apply, differenceRoot_apply, sumRoot_apply, e, f] <;>
    field_simp <;> ring

set_option maxHeartbeats 2500000 in
-- Check one relative root before composing the six conjugation identities.
theorem torus_highestRoot_intertwine (hdeg : Module.finrank F K = 3)
    (h : Kˣ × Fˣ) (p : PositiveParameters F K) :
    torusMap F K h * highestRoot F K p.v =
      highestRoot F K (torusScale F K h p).v * torusMap F K h := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (torusMap F K h).val ((highestRoot F K p.v).val x) =
    (highestRoot F K (torusScale F K h p).v).val ((torusMap F K h).val x)
  have ha : (h.1 : K) ≠ 0 := h.1.ne_zero
  have hb : algebraMap F K (h.2 : F) ≠ 0 := (baseUnit F K h.2).ne_zero
  have ha1 : FiniteCubic.sigma F K (h.1 : K) ≠ 0 := (sigmaUnit F K h.1).ne_zero
  have ha2 : FiniteCubic.sigma F K (FiniteCubic.sigma F K (h.1 : K)) ≠ 0 := (sigmaUnit F K (sigmaUnit F K h.1)).ne_zero
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [torusMap, torusWeights, diagonalEmbedding, diagonalLinear,
      torusScale, sigmaUnit, baseUnit, normUnit, FiniteCubic.norm_formula hdeg,
      FiniteCubic.sigma_cube hdeg, Algebra.smul_def, highestRoot, pinnedRoot,
      Subgroup.coe_mul, LinearEquiv.mul_apply, differenceRoot_apply, sumRoot_apply, e, f] <;>
    field_simp <;> ring

private theorem intertwine_mul {G : Type*} [_root_.Group G] {h a b c d : G}
    (ha : h*a=c*h) (hb : h*b=d*h) : h*(a*b)=(c*d)*h := by
  calc
    _ = (h*a)*b := by group
    _ = c*(h*b) := by rw [ha]; group
    _ = (c*d)*h := by rw [hb]; group

theorem torus_positive_intertwine (hdeg : Module.finrank F K = 3)
    (h : Kˣ × Fˣ) (p : PositiveParameters F K) :
    torusMap F K h * positiveMatrix F K p =
      positiveMatrix F K (torusScale F K h p) * torusMap F K h := by
  exact intertwine_mul (intertwine_mul (intertwine_mul (intertwine_mul
    (intertwine_mul (torus_shortRoot_intertwine F K hdeg h p)
      (torus_longRoot_intertwine F K hdeg h p))
    (torus_nextShortRoot_intertwine F K hdeg h p))
    (torus_middleRoot_intertwine F K hdeg h p))
    (torus_highLongRoot_intertwine F K hdeg h p))
    (torus_highestRoot_intertwine F K hdeg h p)

end Atlas.Triality

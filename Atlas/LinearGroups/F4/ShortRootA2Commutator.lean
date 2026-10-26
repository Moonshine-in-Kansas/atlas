import Atlas.LinearGroups.F4.ShortRoots

/-! A closed short-root A₂ pair with structure constant +1, including characteristic two. -/
namespace Atlas.F4
variable {R : Type*} [CommRing R]

def shortA2BetaApply (s : R) (x : Atlas.Albert.Carrier R) : Atlas.Albert.Carrier R :=
  Atlas.Albert.coordinateCycle (Atlas.Albert.shortRootLinear 0 s
    (Atlas.Albert.coordinateCycle (Atlas.Albert.coordinateCycle x)))

def shortA2GammaApply (t : R) (x : Atlas.Albert.Carrier R) : Atlas.Albert.Carrier R :=
  Atlas.Albert.coordinateCycle (Atlas.Albert.coordinateCycle
    (Atlas.Albert.shortRootLinear 7 t (Atlas.Albert.coordinateCycle x)))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- Symbolic ring identity for β=B₀, γ=A₇ and β+γ=C₃. -/
theorem shortA2_swap (s t : R) (x : Atlas.Albert.Carrier R) :
    shortA2BetaApply s (shortA2GammaApply t x) =
      Atlas.Albert.shortRootLinear 3 (s*t) (shortA2GammaApply t (shortA2BetaApply s x)) := by
  apply Prod.ext
  · funext i; fin_cases i <;>
      simp [Matrix.vecHead, Matrix.vecTail, shortA2BetaApply, shortA2GammaApply,
        Atlas.Albert.coordinateCycle, Atlas.Albert.shortRootLinear, Atlas.Albert.shortRootFormula,
        Atlas.SplitOctonion.basisVector, Pi.single_apply, Atlas.SplitOctonion.mul,
        Atlas.SplitOctonion.conjugate, Atlas.SplitOctonion.trace, Atlas.SplitOctonion.unit] <;> ring
  · funext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecHead, Matrix.vecTail, shortA2BetaApply, shortA2GammaApply,
        Atlas.Albert.coordinateCycle, Atlas.Albert.shortRootLinear, Atlas.Albert.shortRootFormula,
        Atlas.SplitOctonion.basisVector, Pi.single_apply, Atlas.SplitOctonion.mul,
        Atlas.SplitOctonion.conjugate, Atlas.SplitOctonion.trace, Atlas.SplitOctonion.unit] <;> ring

noncomputable section
variable {F : Type*} [Field F]

theorem shortRoot_beta_apply (s : F) (x : Atlas.Albert.Carrier F) :
    (shortRoot 1 0 s).val x = shortA2BetaApply s x := rfl

theorem shortRoot_gamma_apply (t : F) (x : Atlas.Albert.Carrier F) :
    (shortRoot 2 7 t).val x = shortA2GammaApply t x := by
  change Atlas.Albert.coordinateCycle (Atlas.Albert.coordinateCycle
    (Atlas.Albert.shortRootLinear 7 t (Atlas.Albert.coordinateCycle
      (Atlas.Albert.coordinateCycle (Atlas.Albert.coordinateCycle (Atlas.Albert.coordinateCycle x)))))) = _
  rw [Atlas.Albert.coordinateCycle_three] <;> rfl

theorem shortRoot_alpha_apply (t : F) (x : Atlas.Albert.Carrier F) :
    (shortRoot 0 3 t).val x = Atlas.Albert.shortRootLinear 3 t x := rfl

theorem shortRoot_A2_swap (s t : F) :
    shortRoot 1 0 s * shortRoot 2 7 t = shortRoot 0 3 (s*t) * shortRoot 2 7 t * shortRoot 1 0 s := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (shortRoot 1 0 s).val ((shortRoot 2 7 t).val x) =
    (shortRoot 0 3 (s*t)).val ((shortRoot 2 7 t).val ((shortRoot 1 0 s).val x))
  rw [shortRoot_beta_apply, shortRoot_gamma_apply, shortRoot_alpha_apply,
    shortRoot_gamma_apply, shortRoot_beta_apply]
  exact shortA2_swap s t x

theorem shortRoot_A2_commutator (s t : F) :
    shortRoot 1 0 s * shortRoot 2 7 t * (shortRoot 1 0 s)⁻¹ * (shortRoot 2 7 t)⁻¹ =
      shortRoot 0 3 (s*t) := by
  rw [shortRoot_A2_swap]
  simp [mul_assoc]

end
end Atlas.F4

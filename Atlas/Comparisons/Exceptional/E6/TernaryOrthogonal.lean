import Atlas.Comparisons.Exceptional.E6.TernaryAction
import Atlas.LinearGroups.Orthogonal.IsometryTransport

/-! Reduction of the actual Weyl group into the full five-dimensional orthogonal group. -/
noncomputable section
namespace Atlas.Comparisons.E6Lattice
open Atlas.Orthogonal

def ternaryLift (v : Fin 6 → ZMod 3) : Fin 6 → ℤ := fun i => (v i).val

@[simp] theorem reduceTernary_lift (v : Fin 6 → ZMod 3) :
    reduceTernary (ternaryLift v) = v := by
  funext i
  simp [reduceTernary,ternaryLift]

theorem norm_reduceTernary (x : Fin 6 → ℤ) : norm (reduceTernary x) = ((norm x : ℤ) : ZMod 3) := by
  simp [norm,reduceTernary]

theorem ternaryLinear_preserves (g : IntegralWeyl) (v : Fin 6 → ZMod 3) :
    norm (ternaryLinear g v) = norm v := by
  have hf : norm (g.val.val (ternaryLift v)) = norm (ternaryLift v) := by
    simpa only [form_apply] using g.val.property (ternaryLift v)
  have he := norm_reduceTernary (g.val.val (ternaryLift v))
  rw [← ternaryLinear_action,reduceTernary_lift,hf,← norm_reduceTernary,
    reduceTernary_lift] at he
  exact he

theorem ternaryQuotient_preserves (g : IntegralWeyl) (v : Fin 5 → ZMod 3) :
    quotientForm (ternaryQuotientRepresentation g v) = quotientForm v := by
  change form (ZMod 3) (quotientSection
    (quotientCoordinates (ternaryLinear g (quotientSection v)))) =
      form (ZMod 3) (quotientSection v)
  rw [form_apply,form_apply,norm_quotient,ternaryLinear_preserves]

def intoTernaryQuotient : IntegralWeyl →* isometrySubgroup quotientForm :=
  ternaryQuotientRepresentation.codRestrict _ ternaryQuotient_preserves

/-- Removing a nonzero scale changes neither the actual isometries nor their multiplication. -/
def ternaryUnscale : isometrySubgroup ((2 : ZMod 3) • formB 2 (ZMod 3)) ≃*
    isometrySubgroup (formB 2 (ZMod 3)) :=
  MulEquiv.subgroupCongr (by
    ext g
    constructor
    · intro hg x
      have h := hg x
      change (2 : ZMod 3) * formB 2 (ZMod 3) (g x) = 2 * formB 2 (ZMod 3) x at h
      exact (mul_left_cancel₀ (by decide : (2 : ZMod 3) ≠ 0)) h
    · intro hg x
      change (2 : ZMod 3) * formB 2 (ZMod 3) (g x) = 2 * formB 2 (ZMod 3) x
      rw [hg])

def ternaryBEquiv : isometrySubgroup quotientForm ≃* O_B 2 (ZMod 3) :=
  (isometryGroupTransport ternaryQuotientIsometry.symm).trans ternaryUnscale

def intoTernaryB : IntegralWeyl →* O_B 2 (ZMod 3) :=
  ternaryBEquiv.toMonoidHom.comp intoTernaryQuotient

end Atlas.Comparisons.E6Lattice

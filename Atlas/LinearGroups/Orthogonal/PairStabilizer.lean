import Atlas.LinearGroups.Orthogonal.Basic
import Atlas.LinearAlgebra.QuadraticComplementExtension

/-! # The full pointwise hyperbolic-pair stabilizer -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V)

def pairStabilizer : Subgroup (isometrySubgroup Q) where
  carrier := {g | g.val e = e ∧ g.val f = f}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' {g h} hg hh := by
    constructor
    · change g.val (h.val e) = e
      rw [hh.1, hg.1]
    · change g.val (h.val f) = f
      rw [hh.2, hg.2]
  inv_mem' {g} hg := by
    constructor
    · change g.val.symm e = e
      exact g.val.symm_apply_eq.mpr hg.1.symm
    · change g.val.symm f = f
      exact g.val.symm_apply_eq.mpr hg.2.symm

/-- Restrict every full pair-fixer to the actual perpendicular complement. -/
def pairRestriction : pairStabilizer Q e f →* isometrySubgroup (complementForm Q e f) where
  toFun g := (isometryCarrierEquiv _).symm
    (complementTransport Q ((isometryCarrierEquiv Q) g.val) e f e f g.prop.1 g.prop.2)
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl

variable (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

include he hf hef in
theorem pairRestriction_injective : Function.Injective (pairRestriction Q e f) := by
  intro g h hgh
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  let s := split Q e f he hf hef
  have hx := s.symm_apply_apply x
  change (s x).1.1 • e + (s x).1.2 • f + (s x).2.val = x at hx
  have hw : g.val.val (s x).2.val = h.val.val (s x).2.val := by
    have hr := congrArg (fun k : isometrySubgroup (complementForm Q e f) =>
      (k.val (s x).2).val) hgh
    exact hr
  calc
    g.val.val x = g.val.val ((s x).1.1 • e + (s x).1.2 • f + (s x).2.val) := congrArg _ hx.symm
    _ = h.val.val ((s x).1.1 • e + (s x).1.2 • f + (s x).2.val) := by
      simp only [map_add, map_smul, g.prop.1, g.prop.2, h.prop.1, h.prop.2, hw]
    _ = h.val.val x := congrArg _ hx

include he hf hef in
theorem pairRestriction_surjective : Function.Surjective (pairRestriction Q e f) := by
  intro k
  let ki := (isometryCarrierEquiv _ k)
  let g := complementExtension Q e f he hf hef ki
  have hge : g e = e := complementExtension_fix_e Q e f he hf hef ki
  have hgf : g f = f := complementExtension_fix_f Q e f he hf hef ki
  refine ⟨⟨(isometryCarrierEquiv Q).symm g, hge, hgf⟩, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  exact complementExtension_apply Q e f he hf hef ki x

/-- The full stabilizer, not merely a displayed subgroup, is the complement isometry group. -/
def pairStabilizerEquiv : pairStabilizer Q e f ≃* isometrySubgroup (complementForm Q e f) :=
  MulEquiv.ofBijective (pairRestriction Q e f)
    ⟨pairRestriction_injective Q e f he hf hef, pairRestriction_surjective Q e f he hf hef⟩

end Atlas.Orthogonal

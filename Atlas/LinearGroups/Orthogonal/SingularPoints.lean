import Atlas.LinearGroups.Orthogonal.ElementaryPairStandard
import Mathlib.LinearAlgebra.Projectivization.Action

/-! # The actual singular projective points and the elementary action -/
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.Orthogonal
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

theorem singular_mk_iff (v : V) (hv : v ≠ 0) :
    Q (Projectivization.mk F v hv).rep = 0 ↔ Q v = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
  rw [← ha]
  change Q (a.val • v) = 0 ↔ _
  rw [Q.map_smul, smul_eq_mul]
  simp only [mul_eq_zero, a.ne_zero, false_or]

/-- Singular one-dimensional subspaces of the actual quadratic space. -/
def SingularPoints := {p : ℙ F V // Q p.rep = 0}

def singularPointMk (v : V) (hv : v ≠ 0) (hq : Q v = 0) : SingularPoints Q :=
  ⟨Projectivization.mk F v hv, (singular_mk_iff Q v hv).mpr hq⟩

theorem singularPointMk_rep (p : SingularPoints Q) :
    singularPointMk Q p.val.rep p.val.rep_nonzero p.prop = p :=
  Subtype.ext (Projectivization.mk_rep p.val)

instance singularPointsAction : MulAction (isometrySubgroup Q) (SingularPoints Q) where
  smul g p := ⟨g.val • p.val, by
    rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk]
    apply (singular_mk_iff Q _ _).mpr
    exact (g.prop _).trans p.prop⟩
  one_smul p := Subtype.ext (one_smul _ _)
  mul_smul g h p := Subtype.ext (mul_smul g.val h.val p.val)

theorem singularPointMk_smul (g : isometrySubgroup Q) (v : V) (hv : v ≠ 0) (hq : Q v = 0) :
    g • singularPointMk Q v hv hq =
      singularPointMk Q (g.val v) (fun h => hv (g.val.injective (h.trans (map_zero g.val).symm)))
        ((g.prop v).trans hq) := rfl

theorem singularPoints_pretransitive
    (ht : ∀ u v : V, u ≠ 0 → v ≠ 0 → Q u = 0 → Q v = 0 →
      ∃ g : isometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val u = v) :
    MulAction.IsPretransitive (elementarySubgroup Q) (SingularPoints Q) where
  exists_smul_eq p r := by
    obtain ⟨g, hg, hgr⟩ := ht p.val.rep r.val.rep p.val.rep_nonzero r.val.rep_nonzero p.prop r.prop
    refine ⟨⟨g, hg⟩, ?_⟩
    apply Subtype.ext
    change g.val • p.val = r.val
    rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk]
    change Projectivization.mk F (g.val p.val.rep) _ = r.val
    simp only [hgr, Projectivization.mk_rep]

theorem singularPointsB_pretransitive (n : ℕ) (h2 : (2 : F) ≠ 0) :
    MulAction.IsPretransitive (elementarySubgroup (formB (n+2) F))
      (SingularPoints (formB (n+2) F)) :=
  singularPoints_pretransitive _ (elementaryB_singular_transport n h2)
end Atlas.Orthogonal

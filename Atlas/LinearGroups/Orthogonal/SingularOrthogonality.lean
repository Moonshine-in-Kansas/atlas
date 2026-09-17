import Atlas.LinearGroups.Orthogonal.SingularPoints

/-! # Orthogonality on the actual singular projective points -/
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

def SingularPerp (p r : SingularPoints Q) : Prop := Q.polarBilin p.val.rep r.val.rep = 0

theorem singularPerp_symmetric : Symmetric (SingularPerp Q) := by
  intro p r h
  exact (polar_swap Q _ _).trans h

theorem singularPerp_self (p : SingularPoints Q) : SingularPerp Q p p := by
  change Q.polarBilin p.val.rep p.val.rep = 0
  rw [polar_self, p.prop, mul_zero]

theorem singularPerp_mk_iff (u v : V) (hu : u ≠ 0) (hv : v ≠ 0)
    (hqu : Q u = 0) (hqv : Q v = 0) :
    SingularPerp Q (singularPointMk Q u hu hqu) (singularPointMk Q v hv hqv) ↔
      Q.polarBilin u v = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F u hu
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
  change Q.polarBilin (Projectivization.mk F u hu).rep (Projectivization.mk F v hv).rep = 0 ↔ _
  rw [← ha, ← hb]
  change Q.polarBilin (a.val • u) (b.val • v) = 0 ↔ _
  simp only [map_smul, LinearMap.smul_apply]
  simp only [smul_eq_mul, mul_eq_zero, a.ne_zero, b.ne_zero, false_or]

theorem singularPerp_smul_iff (g : isometrySubgroup Q) (p r : SingularPoints Q) :
    SingularPerp Q (g • p) (g • r) ↔ SingularPerp Q p r := by
  rw [← singularPointMk_rep Q p, ← singularPointMk_rep Q r,
    singularPointMk_smul, singularPointMk_smul, singularPerp_mk_iff, singularPerp_mk_iff]
  have h := isometry_polar Q (isometryCarrierEquiv Q g) p.val.rep r.val.rep
  change Q.polarBilin (g.val p.val.rep) (g.val r.val.rep) = Q.polarBilin p.val.rep r.val.rep at h
  exact h ▸ Iff.rfl
end Atlas.Orthogonal

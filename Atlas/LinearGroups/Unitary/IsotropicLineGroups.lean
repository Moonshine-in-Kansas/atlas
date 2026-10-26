import Atlas.LinearGroups.Unitary.IsotropicAction
import Atlas.LinearGroups.Unitary.LineTransvections

/-! # The abelian subgroup of an actual isotropic point stabilizer -/
noncomputable section
namespace Atlas.Unitary
open Matrix
open scoped LinearAlgebra.Projectivization
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

def pointTransvections (hdeg : Module.finrank F K = 2) (p : IsotropicPoints F K n) :
    Subgroup (SU F K n hdeg) := lineTransvections hdeg p.val.rep (isotropic_rep p)

theorem card_pointTransvections (hdeg : Module.finrank F K = 2) (p : IsotropicPoints F K n) :
    Nat.card (pointTransvections hdeg p) = Nat.card F :=
  card_lineTransvections hdeg _ _ p.val.rep_nonzero

instance pointTransvections_commutative (hdeg : Module.finrank F K = 2)
    (p : IsotropicPoints F K n) : IsMulCommutative (pointTransvections hdeg p) :=
  lineTransvections_commutative hdeg _ _

theorem pointTransvections_fix_rep (hdeg : Module.finrank F K = 2)
    (p : IsotropicPoints F K n) (g : SU F K n hdeg) (hg : g ∈ pointTransvections hdeg p) :
    g.val *ᵥ p.val.rep = p.val.rep := by
  obtain ⟨a, rfl⟩ := hg
  change transvectionMatrix (F := F) p.val.rep a.toAdd.val *ᵥ p.val.rep = _
  rw [transvectionMatrix_apply, isotropic_rep, mul_zero, zero_smul, add_zero]

theorem pointTransvections_le_stabilizer (hdeg : Module.finrank F K = 2)
    (p : IsotropicPoints F K n) :
    pointTransvections hdeg p ≤ MulAction.stabilizer (SU F K n hdeg) p := by
  intro g hg
  change g • p = p
  apply Subtype.ext
  change g • p.val = p.val
  rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk]
  have he : g • p.val.rep = p.val.rep := pointTransvections_fix_rep hdeg p g hg
  simp only [he]

theorem pointTransvections_normal (hdeg : Module.finrank F K = 2)
    (p : IsotropicPoints F K n) :
    ((pointTransvections hdeg p).subgroupOf (MulAction.stabilizer (SU F K n hdeg) p)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (pointTransvections_le_stabilizer hdeg p)).mpr
  intro g hg
  have he := congrArg Subtype.val (show g • p = p from hg)
  change g • p.val = p.val at he
  rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff] at he
  obtain ⟨c, hc⟩ := he
  exact line_preserver_mem_normalizer hdeg _ _ g c c.ne_zero hc.symm

/-- A line transvection which is central is the identity, uniformly in small fields. -/
theorem pointTransvections_center_trivial (hdeg : Module.finrank F K = 2) (hn : 0 < n)
    (p : IsotropicPoints F K n) (g : SU F K n hdeg)
    (hg : g ∈ pointTransvections hdeg p) (hz : g ∈ Subgroup.center (SU F K n hdeg)) :
    g = 1 := by
  obtain ⟨c, hc⟩ := central_matrix_scalar hdeg hn g hz
  have hfix := pointTransvections_fix_rep hdeg p g hg
  have hs : c • p.val.rep = p.val.rep := by
    simpa [hc, Matrix.mulVec_diagonal] using hfix
  have hc1 : c = 1 := smul_left_injective K p.val.rep_nonzero (hs.trans (one_smul K _).symm)
  apply Subtype.ext
  simpa [hc1] using hc

/-- The same line group survives faithfully in the actual PSU quotient. -/
def projectivePointTransvections (hdeg : Module.finrank F K = 2)
    (p : IsotropicPoints F K n) : Subgroup (PSU F K n hdeg) :=
  (pointTransvections hdeg p).map (projection F K n hdeg)

def pointProjection (hdeg : Module.finrank F K = 2) (p : IsotropicPoints F K n) :
    pointTransvections hdeg p →* PSU F K n hdeg :=
  (projection F K n hdeg).comp (pointTransvections hdeg p).subtype

theorem pointProjection_injective (hdeg : Module.finrank F K = 2) (hn : 0 < n)
    (p : IsotropicPoints F K n) : Function.Injective (pointProjection hdeg p) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  have he : projection F K n hdeg g.val = 1 := hg
  have hz : g.val ∈ Subgroup.center (SU F K n hdeg) := by
    rw [← projection_kernel F K n hdeg]
    exact he
  have hg1 := pointTransvections_center_trivial hdeg hn p g.val g.prop hz
  exact Subtype.ext hg1

theorem card_projectivePointTransvections (hdeg : Module.finrank F K = 2) (hn : 0 < n)
    (p : IsotropicPoints F K n) : Nat.card (projectivePointTransvections hdeg p) = Nat.card F := by
  have hr : (pointProjection hdeg p).range = projectivePointTransvections hdeg p := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.val, g.prop, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective
    (pointProjection_injective hdeg hn p)).toEquiv]
  exact card_pointTransvections hdeg p

instance projectivePointTransvections_commutative (hdeg : Module.finrank F K = 2)
    (p : IsotropicPoints F K n) : IsMulCommutative (projectivePointTransvections hdeg p) :=
  inferInstanceAs (IsMulCommutative ((pointTransvections hdeg p).map (projection F K n hdeg)))
end Atlas.Unitary

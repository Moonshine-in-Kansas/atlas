import Atlas.LinearGroups.Orthogonal.Center
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.IsPerfect

/-! # Quotienting the actual elementary group by its actual scalar isometries -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

def elementaryScalarSubgroup : Subgroup (elementarySubgroup Q) where
  carrier := {z | ∃ c : F, c^2 = 1 ∧ ∀ x, z.val.val x = c • x}
  one_mem' := ⟨1, one_pow 2, fun x => (one_smul F x).symm⟩
  mul_mem' := by
    rintro z t ⟨c, hc, hcz⟩ ⟨d, hd, hdt⟩
    refine ⟨c*d, by rw [mul_pow, hc, hd, one_mul], ?_⟩
    intro x
    change z.val.val (t.val.val x) = (c*d) • x
    rw [hdt, map_smul, hcz, smul_smul, mul_comm]
  inv_mem' := by
    rintro z ⟨c, hc, hcz⟩
    refine ⟨c, hc, ?_⟩
    intro x
    change z.val.val.symm x = c • x
    apply z.val.val.injective
    rw [LinearEquiv.apply_symm_apply, hcz, smul_smul, ← pow_two, hc, one_smul]

theorem elementaryScalarSubgroup_le_center :
    elementaryScalarSubgroup Q ≤ Subgroup.center (elementarySubgroup Q) := by
  rintro z ⟨c, _, hc⟩
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val.val (z.val.val x) = z.val.val (g.val.val x)
  rw [hc, hc, map_smul]

instance elementaryScalarSubgroup_normal : (elementaryScalarSubgroup Q).Normal where
  conj_mem z hz g := by
    have h := (Subgroup.mem_center_iff.mp (elementaryScalarSubgroup_le_center Q hz)) g
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
    exact hz

theorem elementaryScalarSubgroup_eq_center (H : WittTwoFrame Q)
    (hQ : Q.polarBilin.Nondegenerate) :
    elementaryScalarSubgroup Q = Subgroup.center (elementarySubgroup Q) := by
  ext z
  exact (mem_elementary_center_iff_scalar Q H hQ z).symm

/-- The scalar quotient of the actual elementary carrier, independent of simplicity. -/
def ProjectiveElementary := elementarySubgroup Q ⧸ elementaryScalarSubgroup Q

instance projectiveElementaryGroup : Group (ProjectiveElementary Q) :=
  inferInstanceAs (Group (elementarySubgroup Q ⧸ elementaryScalarSubgroup Q))

instance projectiveElementaryFinite [Finite (elementarySubgroup Q)] : Finite (ProjectiveElementary Q) :=
  inferInstanceAs (Finite (elementarySubgroup Q ⧸ elementaryScalarSubgroup Q))

def projectiveElementaryMap : elementarySubgroup Q →* ProjectiveElementary Q :=
  QuotientGroup.mk' (elementaryScalarSubgroup Q)

theorem projectiveElementaryMap_surjective : Function.Surjective (projectiveElementaryMap Q) :=
  QuotientGroup.mk'_surjective _

theorem projectiveElementaryMap_kernel : (projectiveElementaryMap Q).ker = elementaryScalarSubgroup Q :=
  QuotientGroup.ker_mk' _

def projectiveElementaryCenterEquiv (H : WittTwoFrame Q) (hQ : Q.polarBilin.Nondegenerate) :
    ProjectiveElementary Q ≃* (elementarySubgroup Q ⧸ Subgroup.center (elementarySubgroup Q)) :=
  QuotientGroup.quotientMulEquivOfEq (elementaryScalarSubgroup_eq_center Q H hQ)

theorem projectiveElementary_perfect [Group.IsPerfect (elementarySubgroup Q)] :
    Group.IsPerfect (ProjectiveElementary Q) :=
  Group.IsPerfect.ofSurjective (f := projectiveElementaryMap Q) (projectiveElementaryMap_surjective Q)
end Atlas.Orthogonal

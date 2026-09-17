import Atlas.LinearGroups.Symplectic.ProjectiveGeneration
import Atlas.LinearGroups.Symplectic.Nontrivial
import Mathlib.GroupTheory.GroupAction.Iwasawa

noncomputable section
open scoped Pointwise LinearAlgebra.Projectivization
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

def parameterHom (v : Vector n F) : Multiplicative F →* Sp n F where
  toFun a := transvection v a.toAdd
  map_one' := transvection_zero v
  map_mul' a b := transvection_add v a.toAdd b.toAdd

def directionGroup (v : Vector n F) : Subgroup (PSp n F) :=
  (projection.comp (parameterHom v)).range

theorem mem_directionGroup (v : Vector n F) (g : PSp n F) :
    g ∈ directionGroup v ↔ ∃ a : F, projection (transvection v a) = g := Iff.rfl

theorem directionGroup_scale (v : Vector n F) (c : F) (hc : c ≠ 0) :
    directionGroup (c • v) = directionGroup v := by
  ext g
  rw [mem_directionGroup,mem_directionGroup]
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨c^2*a,by rw [transvection_scale]⟩
  · rintro ⟨a,rfl⟩
    refine ⟨a/c^2,?_⟩
    rw [transvection_scale,mul_div_cancel₀ a (pow_ne_zero _ hc)]

theorem directionGroup_conj (g : Sp n F) (v : Vector n F) :
    directionGroup (g • v) = MulAut.conj (projection g) • directionGroup v := by
  ext t
  constructor
  · rintro ⟨a,rfl⟩
    refine ⟨projection (transvection v a.toAdd),⟨a,rfl⟩,?_⟩
    change projection g * projection (transvection v a.toAdd) * (projection g)⁻¹ = _
    rw [← map_inv,← map_mul,← map_mul,transvection_conjugate]
    rfl
  · rintro ⟨t,⟨a,rfl⟩,rfl⟩
    refine ⟨a,?_⟩
    change projection (transvection (g • v) a.toAdd) =
      projection g * projection (transvection v a.toAdd) * (projection g)⁻¹
    rw [← map_inv,← map_mul,← map_mul,transvection_conjugate]

/-- Actual projective transvections with a fixed direction line. -/
def lineTransvections (p : Points n F) : Subgroup (PSp n F) := directionGroup p.rep

theorem lineTransvections_abelian (p : Points n F) : IsMulCommutative (lineTransvections p) :=
  Subgroup.range_isMulCommutative _

theorem lineTransvections_mk {v : Vector n F} (hv : v ≠ 0) :
    lineTransvections (Projectivization.mk F v hv) = directionGroup v := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
  unfold lineTransvections
  rw [← ha,Units.smul_def,directionGroup_scale v a.val a.ne_zero]

theorem lineTransvections_conj (g : PSp n F) (p : Points n F) :
    lineTransvections (g • p) = MulAut.conj g • lineTransvections p := by
  obtain ⟨g,rfl⟩ := projection_surjective g
  rw [projection_smul,← Projectivization.mk_rep p,Projectivization.smul_mk,
    lineTransvections_mk,directionGroup_conj,lineTransvections_mk]

theorem lineTransvections_generate : (⨆ p : Points n F,lineTransvections p) = ⊤ := by
  apply top_unique
  rw [← projectiveTransvectionGroup_eq_top (n := n) (F := F)]
  apply (Subgroup.closure_le _).mpr
  rintro t ⟨v,a,rfl⟩
  by_cases hv : v=0
  · subst v
    simp
  · have hmem : projection (transvection v a) ∈ lineTransvections (Projectivization.mk F v hv) := by
      rw [lineTransvections_mk,mem_directionGroup]
      exact ⟨a,rfl⟩
    exact (le_iSup lineTransvections (Projectivization.mk F v hv)) hmem

theorem lineTransvections_le_stabilizer (p : Points n F) :
    lineTransvections p ≤ MulAction.stabilizer (PSp n F) p := by
  rintro g ⟨a,rfl⟩
  change projection (transvection p.rep a.toAdd) • p = p
  rw [projection_smul,← Projectivization.mk_rep p,Projectivization.smul_mk]
  simp [transvection_apply]

theorem lineTransvections_normal (p : Points n F) :
    ((lineTransvections p).subgroupOf (MulAction.stabilizer (PSp n F) p)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (lineTransvections_le_stabilizer p)).mpr
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg a ha
  have hc : MulAut.conj g • lineTransvections p = lineTransvections p := by
    rw [← lineTransvections_conj,MulAction.mem_stabilizer_iff.mp hg]
  rw [← hc]
  exact ⟨a,ha,rfl⟩

theorem projective_parameter_injective {v : Vector n F} (hv : v ≠ 0) :
    Function.Injective (projection.comp (parameterHom v)) := by
  intro a b hab
  have hab' : projection (transvection v a.toAdd) = projection (transvection v b.toAdd) := hab
  have he : a.toAdd=b.toAdd := by
    by_contra hne
    apply projection_transvection_ne_one hv (sub_ne_zero.mpr hne)
    rw [sub_eq_add_neg,transvection_add,map_mul,← transvection_inverse,map_inv,hab',mul_inv_cancel]
  exact congrArg Multiplicative.ofAdd he

theorem card_lineTransvections [Finite F] (p : Points n F) :
    Nat.card (lineTransvections p) = Nat.card F := by
  exact (Nat.card_congr (MonoidHom.ofInjective (projective_parameter_injective p.rep_nonzero)).toEquiv).symm

def iwasawa : MulAction.IwasawaStructure (PSp n F) (Points n F) where
  T := lineTransvections
  is_comm := lineTransvections_abelian
  is_conj := lineTransvections_conj
  is_generator := lineTransvections_generate

end Atlas.Symplectic

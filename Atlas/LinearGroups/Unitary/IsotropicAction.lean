import Atlas.LinearGroups.Unitary.Center
import Mathlib.LinearAlgebra.Projectivization.Action

/-! # The faithful action of actual PSU on isotropic lines

The action kernel is proved directly from the isotropic-line scalar criterion,
without generation, transitivity or simplicity assumptions.
-/
noncomputable section
namespace Atlas.Unitary
open Matrix
open scoped LinearAlgebra.Projectivization
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

instance specialVectorAction (hdeg : Module.finrank F K = 2) :
    DistribMulAction (SU F K n hdeg) (Fin n → K) where
  smul g v := g.val *ᵥ v
  one_smul := Matrix.one_mulVec
  mul_smul g h v := (Matrix.mulVec_mulVec v g.val h.val).symm
  smul_zero g := Matrix.mulVec_zero g.val
  smul_add g v w := Matrix.mulVec_add g.val v w

instance specialVectorScalarComm (hdeg : Module.finrank F K = 2) :
    SMulCommClass (SU F K n hdeg) K (Fin n → K) where
  smul_comm g a v := Matrix.mulVec_smul g.val a v

/-- Isotropy of an actual projective line, independent of its representative. -/
def IsotropicLine (F K : Type*) [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] {n : ℕ} (p : ℙ K (Fin n → K)) : Prop :=
  ∃ (v : Fin n → K) (hv : v ≠ 0), p = Projectivization.mk K v hv ∧ hermitian F K v v = 0

theorem isotropicLine_mk (v : Fin n → K) (hv : v ≠ 0) :
    IsotropicLine F K (Projectivization.mk K v hv) ↔ hermitian F K v v = 0 := by
  constructor
  · rintro ⟨w, hw, hp, hww⟩
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K v w hv hw).mp hp
    rw [← ha]
    simp [Units.smul_def, hermitian_smul_left, hermitian_smul_right, hww]
  · intro h
    exact ⟨v, hv, rfl, h⟩

/-- The actual isotropic one-dimensional K-subspaces of the standard Hermitian space. -/
def IsotropicPoints (F K : Type*) [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (n : ℕ) := {p : ℙ K (Fin n → K) // IsotropicLine F K p}

def isotropicPoint (v : Fin n → K) (hv : v ≠ 0) (hvv : hermitian F K v v = 0) :
    IsotropicPoints F K n := ⟨Projectivization.mk K v hv, (isotropicLine_mk v hv).mpr hvv⟩

theorem isotropic_rep (p : IsotropicPoints F K n) :
    hermitian F K p.val.rep p.val.rep = 0 := by
  apply (isotropicLine_mk p.val.rep p.val.rep_nonzero).mp
  simpa using p.prop

theorem isotropicLine_smul (hdeg : Module.finrank F K = 2)
    (g : SU F K n hdeg) (p : ℙ K (Fin n → K)) (hp : IsotropicLine F K p) :
    IsotropicLine F K (g • p) := by
  obtain ⟨v, hv, rfl, hvv⟩ := hp
  rw [Projectivization.smul_mk, isotropicLine_mk]
  exact (u_preserves_hermitian hdeg (⟨g.val, g.prop.1⟩ : U F K n hdeg) v v).trans hvv

instance specialIsotropicAction (hdeg : Module.finrank F K = 2) :
    MulAction (SU F K n hdeg) (IsotropicPoints F K n) where
  smul g p := ⟨g • p.val, isotropicLine_smul hdeg g p.val p.prop⟩
  one_smul p := Subtype.ext (one_smul _ p.val)
  mul_smul g h p := Subtype.ext (mul_smul g h p.val)

theorem fixes_isotropic_iff_central (hdeg : Module.finrank F K = 2) (hn : 0 < n)
    (g : SU F K n hdeg) :
    (∀ p : IsotropicPoints F K n, g • p = p) ↔ g ∈ Subgroup.center (SU F K n hdeg) := by
  constructor
  · intro hg
    obtain ⟨c, hc⟩ := matrix_scalar_of_isotropic_lines hdeg hn g.val (by
      intro v hv hvv
      have h := congrArg Subtype.val (hg (isotropicPoint v hv hvv))
      change g • Projectivization.mk K v hv = Projectivization.mk K v hv at h
      rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at h
      obtain ⟨c, hc⟩ := h
      exact ⟨c, hc.symm⟩)
    obtain ⟨a, ha⟩ := scalar_matrix_parameter hdeg hn g c hc
    rw [← ha]
    exact scalarSpecial_mem_center F K hdeg n a
  · intro hg p
    apply Subtype.ext
    obtain ⟨c, hc⟩ := central_matrix_scalar hdeg hn g hg
    change g • p.val = p.val
    rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk,
      Projectivization.mk_eq_mk_iff']
    refine ⟨c, ?_⟩
    change c • p.val.rep = g.val *ᵥ p.val.rep
    rw [hc]
    ext i
    simp [Matrix.mulVec_diagonal]

def isotropicPerm (hdeg : Module.finrank F K = 2) :
    SU F K n hdeg →* Equiv.Perm (IsotropicPoints F K n) := MulAction.toPermHom _ _

theorem isotropicPerm_kernel (hdeg : Module.finrank F K = 2) (hn : 0 < n) :
    (isotropicPerm hdeg (n := n)).ker = Subgroup.center (SU F K n hdeg) := by
  ext g
  change isotropicPerm hdeg g = 1 ↔ _
  rw [Equiv.Perm.ext_iff]
  exact fixes_isotropic_iff_central hdeg hn g

def projectiveIsotropicPerm (hdeg : Module.finrank F K = 2) (hn : 0 < n) :
    PSU F K n hdeg →* Equiv.Perm (IsotropicPoints F K n) :=
  QuotientGroup.lift _ (isotropicPerm hdeg) (by rw [isotropicPerm_kernel hdeg hn])

def isotropicAction (hdeg : Module.finrank F K = 2) (hn : 0 < n) :
    MulAction (PSU F K n hdeg) (IsotropicPoints F K n) :=
  MulAction.compHom _ (projectiveIsotropicPerm hdeg hn)

theorem isotropicAction_faithful (hdeg : Module.finrank F K = 2) (hn : 0 < n) :
    letI := isotropicAction hdeg hn
    FaithfulSMul (PSU F K n hdeg) (IsotropicPoints F K n) := by
  letI := isotropicAction hdeg hn
  apply faithfulSMul_iff.mpr
  intro g hg
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SU F K n hdeg)) g
  apply (QuotientGroup.eq_one_iff _).mpr
  exact (fixes_isotropic_iff_central hdeg hn h).mp hg
end Atlas.Unitary

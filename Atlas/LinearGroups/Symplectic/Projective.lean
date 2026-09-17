import Atlas.LinearGroups.Symplectic.Center
import Mathlib.LinearAlgebra.Projectivization.Action

noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

abbrev Points (n : ℕ) (F : Type*) [Field F] := ℙ F (Vector n F)

theorem fixes_points_iff_central (g : Sp n F) :
    (∀ p : Points n F, g • p = p) ↔ g ∈ Subgroup.center (Sp n F) := by
  constructor
  · intro hg
    obtain ⟨a,ha⟩ := (toLinear g).toLinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
      (fun v => by
        by_cases hv : v = 0
        · simp [hv,linearIndependent_fin2]
        · rw [LinearIndependent.pair_iff' hv]
          have h := hg (Projectivization.mk F v hv)
          rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at h
          obtain ⟨a,ha⟩ := h
          exact fun hli => hli a ha)
    apply scalar_is_central g a
    intro x
    exact congrArg (fun l : Vector n F →ₗ[F] Vector n F => l x) ha
  · intro hg p
    obtain ⟨a,ha⟩ := central_is_scalar g hg
    rw [← Projectivization.mk_rep p,Projectivization.smul_mk,Projectivization.mk_eq_mk_iff']
    exact ⟨a,(ha p.rep).symm⟩

def pointPerm : Sp n F →* Equiv.Perm (Points n F) := MulAction.toPermHom _ _

theorem pointPerm_kernel : (pointPerm (n := n) (F := F)).ker = Subgroup.center (Sp n F) := by
  ext g
  change pointPerm g = 1 ↔ _
  rw [Equiv.Perm.ext_iff]
  exact fixes_points_iff_central g

def projectivePerm : PSp n F →* Equiv.Perm (Points n F) :=
  QuotientGroup.lift _ pointPerm (by rw [pointPerm_kernel])

instance projectiveAction : MulAction (PSp n F) (Points n F) :=
  MulAction.compHom (Points n F) projectivePerm

@[simp] theorem projection_smul (g : Sp n F) (p : Points n F) :
    projection g • p = g • p := rfl

instance projective_faithful : FaithfulSMul (PSp n F) (Points n F) := by
  apply faithfulSMul_iff.mpr
  intro g hg
  obtain ⟨h,rfl⟩ := projection_surjective g
  apply (QuotientGroup.eq_one_iff _).mpr
  exact (fixes_points_iff_central h).mp hg

end Atlas.Symplectic

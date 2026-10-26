import Atlas.LinearGroups.Orthogonal.ReflectionGroup
import Atlas.LinearGroups.Orthogonal.IsometryTransport
import Atlas.LinearAlgebra.QuadraticComplementWitness

/-! Quadratic-space isometries transport reflections and their generated subgroup. -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
variable {Q : QuadraticForm F V} {R : QuadraticForm F W}

theorem isometryGroupTransport_reflection (i : Q.IsometryEquiv R) (a : V)
    (ha : Q a ≠ 0) :
    isometryGroupTransport i (reflectionElement Q a ha) =
      reflectionElement R (i a) (by rw [i.map_app]; exact ha) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change i (reflectionLinear Q a ha (i.symm x)) = reflectionLinear R (i a) (by rw [i.map_app]; exact ha) x
  simp only [reflectionLinear_apply, map_sub, map_smul, i.map_app]
  have hp := isometry_between_polar Q R i (i.symm x) a
  rw [i.apply_symm_apply] at hp
  rw [hp, i.apply_symm_apply]

theorem isometryGroupTransport_mem_reflections (i : Q.IsometryEquiv R)
    (g : isometrySubgroup Q) (hg : g ∈ reflectionSubgroup Q) :
    isometryGroupTransport i g ∈ reflectionSubgroup R := by
  have hle : reflectionSubgroup Q ≤
      (reflectionSubgroup R).comap (isometryGroupTransport i).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro k ⟨a,ha,rfl⟩
    change isometryGroupTransport i (reflectionElement Q a ha) ∈ reflectionSubgroup R
    rw [isometryGroupTransport_reflection]
    exact reflectionElement_mem _ _ _
  exact hle hg

theorem reflectionSubgroup_eq_top_of_isometry (i : Q.IsometryEquiv R)
    (h : reflectionSubgroup R = ⊤) : reflectionSubgroup Q = ⊤ := by
  apply top_unique
  intro g _
  have hg : isometryGroupTransport i g ∈ reflectionSubgroup R := by rw [h]; trivial
  have hm := isometryGroupTransport_mem_reflections i.symm _ hg
  have he : isometryGroupTransport i.symm (isometryGroupTransport i g) = g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change i.symm (i (g.val (i.symm (i x)))) = g.val x
    rw [i.symm_apply_apply, i.symm_apply_apply]
  rwa [he] at hm

end Atlas.Orthogonal

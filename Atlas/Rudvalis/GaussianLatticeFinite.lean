import Atlas.Rudvalis.GaussianLatticeGroup
import Atlas.Rudvalis.LatticeCrossCount

namespace Atlas.Rudvalis

instance : MulAction gaussianLatticeGroup MinimalShell where
  smul g v := ⟨⟨g.val v.val.val,(g.prop.2.1 _).mp v.val.prop⟩,
    (g.prop.1 _ _).trans v.prop⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

noncomputable def gaussianShellHom : gaussianLatticeGroup →* Equiv.Perm MinimalShell :=
  MulAction.toPermHom _ _

theorem gaussianShellHom_injective : Function.Injective gaussianShellHom := by
  intro g h he
  apply Subtype.ext
  apply coordinate_action_determines
  intro i
  let v : MinimalShell := ⟨⟨coordinateMinimum i,coordinateMinimum_mem i⟩,coordinateMinimum_norm i⟩
  exact congrArg (fun w : MinimalShell => w.val.val) (Equiv.congr_fun he v)

instance : Finite gaussianLatticeGroup := Finite.of_injective gaussianShellHom gaussianShellHom_injective

/-- Finiteness comes from the actual shell action, without a target group order. -/
theorem gaussianLatticeGroup_finite : Finite gaussianLatticeGroup := inferInstance

end Atlas.Rudvalis

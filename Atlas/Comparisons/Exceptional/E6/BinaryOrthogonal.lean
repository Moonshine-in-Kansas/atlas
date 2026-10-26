import Atlas.Comparisons.Exceptional.E6.MatrixReduction

/-! Binary reduction lands in the full isometry group of the concrete E6 form. -/
noncomputable section
namespace Atlas.Comparisons.E6Lattice
open Matrix

def binaryLift (v : Fin 6 → ZMod 2) : Fin 6 → ℤ := fun i => (v i).val

@[simp] theorem reduceBinary_lift (v : Fin 6 → ZMod 2) :
    reduceBinary (binaryLift v) = v := by
  funext i
  simp [reduceBinary,binaryLift]

theorem binaryMatrix_preserves (g : IntegralWeyl) (v : Fin 6 → ZMod 2) :
    norm ((binaryMatrix g).val *ᵥ v) = norm v := by
  have hf : norm (g.val.val (binaryLift v)) = norm (binaryLift v) := by
    simpa only [form_apply] using g.val.property (binaryLift v)
  have he := norm_reduceBinary (g.val.val (binaryLift v))
  rw [← binaryMatrix_action,reduceBinary_lift,hf,← norm_reduceBinary,
    reduceBinary_lift] at he
  exact he

def binaryCoordinatesEquiv : GeneralLinearGroup (Fin 6) (ZMod 2) ≃*
    ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) :=
  GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 6 → ZMod 2))

/-- Faithful reduction into the actual full binary isometry group. Surjectivity is separate. -/
def intoBinaryOrthogonal : IntegralWeyl →*
    Atlas.Orthogonal.isometrySubgroup (form (ZMod 2)) :=
  (binaryCoordinatesEquiv.toMonoidHom.comp binaryMatrix).codRestrict _ (fun g => by
    intro v
    change form (ZMod 2) (binaryCoordinatesEquiv (binaryMatrix g) v) = form (ZMod 2) v
    simp only [form_apply]
    exact binaryMatrix_preserves g v)

theorem intoBinaryOrthogonal_injective : Function.Injective intoBinaryOrthogonal := by
  intro g h he
  exact binaryMatrix_injective (binaryCoordinatesEquiv.injective (congrArg Subtype.val he))

instance : Finite IntegralWeyl := Finite.of_injective binaryMatrix binaryMatrix_injective

end Atlas.Comparisons.E6Lattice

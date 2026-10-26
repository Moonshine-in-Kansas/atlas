import Atlas.Sporadic.Janko1.GeneratorActions

/-! Faithful matrix coordinates for the existing octonion automorphisms. -/
namespace Atlas.Janko1

def coordinateRepresentation : G2.Model Field →* Matrix (Fin 8) (Fin 8) Field :=
  LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp
    ((wilsonEquiv.symm.conjRingEquiv).toMonoidHom.comp linearRepresentation)

theorem coordinateRepresentation_injective : Function.Injective coordinateRepresentation :=
  LinearMap.toMatrixAlgEquiv'.injective.comp
    (wilsonEquiv.symm.conjRingEquiv.injective.comp linearRepresentation_injective)

theorem coordinateRepresentation_generator (g : Fin 4) :
    coordinateRepresentation (generator g) = generatorMatrix g := by
  apply Matrix.toLin'.injective
  change Matrix.toLin' (LinearMap.toMatrix'
    (wilsonEquiv.symm.conjRingEquiv (generatorLinear g))) = generatorCoordinates g
  rw [Matrix.toLin'_toMatrix']
  change wilsonEquiv.symm.conj (generatorLinear g) = generatorCoordinates g
  apply LinearMap.ext
  intro x
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
    generatorLinear_coordinates, LinearEquiv.symm_apply_apply]

@[simp] theorem coordinateRepresentation_P : coordinateRepresentation P = generatorMatrix 0 :=
  coordinateRepresentation_generator 0
@[simp] theorem coordinateRepresentation_Q : coordinateRepresentation Q = generatorMatrix 1 :=
  coordinateRepresentation_generator 1
@[simp] theorem coordinateRepresentation_R : coordinateRepresentation R = generatorMatrix 2 :=
  coordinateRepresentation_generator 2
@[simp] theorem coordinateRepresentation_S : coordinateRepresentation S = generatorMatrix 3 :=
  coordinateRepresentation_generator 3

end Atlas.Janko1

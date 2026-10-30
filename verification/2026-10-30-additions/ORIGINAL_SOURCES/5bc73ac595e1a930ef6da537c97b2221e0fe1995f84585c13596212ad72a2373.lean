import F4Work.F4AlbertMatrixInterface
import F4Work.F4Conjugation
import F4Work.F4GeckRepresentation
import Atlas.LinearAlgebra.FaithfulConjugationLift

/-! Actual full Albert stabilizer transformations lifting the eight Chevalley root groups.
This surjection is constructed before either finite order is used. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.F4
open Atlas.LinearAlgebra F4Data
variable (K : Type*) [Field K]

theorem albert_X_compatible (i : Fin 4) (t : K) (v : Fin 52 → K) :
    albertMatrixHom K (albertSimple (F:=K) (Fin.castAdd 4 i) t) * matrixEmbedding K v *
        albertMatrixHom K (albertSimple (F:=K) (Fin.castAdd 4 i) t)⁻¹ =
      matrixEmbedding K (geckRepresentation K (modelX .F4 K i t) v) := by
  rw [albertMatrixHom_simple, albertMatrixHom_simple_inv,
    geckRepresentation_apply, chevalleyMatrixHom_X]
  simpa only [simplePolynomialMatrix, simpleOver] using
    simpleOver_conjugation K (Fin.castAdd 4 i) t v

theorem albert_Y_compatible (i : Fin 4) (t : K) (v : Fin 52 → K) :
    albertMatrixHom K (albertSimple (F:=K) (Fin.natAdd 4 i) t) * matrixEmbedding K v *
        albertMatrixHom K (albertSimple (F:=K) (Fin.natAdd 4 i) t)⁻¹ =
      matrixEmbedding K (geckRepresentation K (modelY .F4 K i t) v) := by
  rw [albertMatrixHom_simple, albertMatrixHom_simple_inv,
    geckRepresentation_apply, chevalleyMatrixHom_Y]
  simpa only [simplePolynomialMatrix, simpleOver] using
    simpleOver_conjugation K (Fin.natAdd 4 i) t v

def albertLiftSubgroup : Subgroup (Atlas.F4.Model K) :=
  conjugationLiftSubgroup (albertMatrixHom K) (matrixEmbedding K) (geckRepresentation K).range

def albertLiftHom : albertLiftSubgroup K →* Model .F4 K :=
  faithfulConjugationLiftHom (albertMatrixHom K) (matrixEmbedding K) (geckRepresentation K)
    (matrixEmbedding_injective K) (geckRepresentation_injective K)

def liftedX (i : Fin 4) (t : K) : albertLiftSubgroup K :=
  ⟨albertSimple (F:=K) (Fin.castAdd 4 i) t,
    ⟨⟨geckRepresentation K (modelX .F4 K i t), ⟨modelX .F4 K i t, rfl⟩⟩,
      albert_X_compatible K i t⟩⟩

def liftedY (i : Fin 4) (t : K) : albertLiftSubgroup K :=
  ⟨albertSimple (F:=K) (Fin.natAdd 4 i) t,
    ⟨⟨geckRepresentation K (modelY .F4 K i t), ⟨modelY .F4 K i t, rfl⟩⟩,
      albert_Y_compatible K i t⟩⟩

theorem albertLiftHom_X (i : Fin 4) (t : K) :
    albertLiftHom K (liftedX K i t) = modelX .F4 K i t :=
  faithfulConjugationLiftHom_eq (albertMatrixHom K) (matrixEmbedding K) (geckRepresentation K)
    (matrixEmbedding_injective K) (geckRepresentation_injective K) _ _ (albert_X_compatible K i t)

theorem albertLiftHom_Y (i : Fin 4) (t : K) :
    albertLiftHom K (liftedY K i t) = modelY .F4 K i t :=
  faithfulConjugationLiftHom_eq (albertMatrixHom K) (matrixEmbedding K) (geckRepresentation K)
    (matrixEmbedding_injective K) (geckRepresentation_injective K) _ _ (albert_Y_compatible K i t)

theorem albertLiftHom_surjective : Function.Surjective (albertLiftHom K) := by
  apply adjointHom_surjective_of_root_lifts
    (rootDatum .F4).pairing (rootDatum .F4).base K (albertLiftHom K)
    (fun i t => liftedX K ((rootDatum .F4).indexEquiv.symm i) t)
    (fun i t => liftedY K ((rootDatum .F4).indexEquiv.symm i) t)
  · intro i t
    obtain ⟨k, rfl⟩ := (rootDatum .F4).indexEquiv.surjective i
    simpa only [Equiv.symm_apply_apply, modelX] using albertLiftHom_X K k t
  · intro i t
    obtain ⟨k, rfl⟩ := (rootDatum .F4).indexEquiv.surjective i
    simpa only [Equiv.symm_apply_apply, modelY] using albertLiftHom_Y K k t

end Atlas.Chevalley.Comparison.F4

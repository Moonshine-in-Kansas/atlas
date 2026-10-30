import Atlas.LinearGroups.Chevalley.Comparison.G2.OctonionRootMatrices
import Atlas.LinearGroups.Chevalley.Comparison.G2.OctonionIntertwiner
import Atlas.LinearGroups.Chevalley.Comparison.G2.GeckRepresentation
import Atlas.LinearAlgebra.FaithfulConjugationLift

/-! Actual octonion automorphisms lifting the four Chevalley root groups.
This surjection is constructed before either finite order is used. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.G2
open Atlas.LinearAlgebra G2Data
variable (K : Type*) [Field K]

theorem octonion_X_compatible (i : Fin 2) (t : K) (v : Fin 14 → K) :
    faithfulMatrixHom8 K (octonionSimpleRoot K (Fin.castAdd 2 i) t) * gamma K v *
        faithfulMatrixHom8 K (octonionSimpleRoot K (Fin.castAdd 2 i) t)⁻¹ =
      gamma K (geckRepresentation K (modelX .G2 K i t) v) := by
  rw [faithfulMatrixHom8_simpleRoot, faithfulMatrixHom8_simpleRoot_inverse,
    geckRepresentation_apply, matrixHom_X]
  exact conjugation_gamma K (Fin.castAdd 2 i) t v

theorem octonion_Y_compatible (i : Fin 2) (t : K) (v : Fin 14 → K) :
    faithfulMatrixHom8 K (octonionSimpleRoot K (Fin.natAdd 2 i) t) * gamma K v *
        faithfulMatrixHom8 K (octonionSimpleRoot K (Fin.natAdd 2 i) t)⁻¹ =
      gamma K (geckRepresentation K (modelY .G2 K i t) v) := by
  rw [faithfulMatrixHom8_simpleRoot, faithfulMatrixHom8_simpleRoot_inverse,
    geckRepresentation_apply, matrixHom_Y]
  exact conjugation_gamma K (Fin.natAdd 2 i) t v

def octonionLiftSubgroup : Subgroup (Atlas.G2.Model K) :=
  conjugationLiftSubgroup (faithfulMatrixHom8 K) (gamma K) (geckRepresentation K).range

def octonionLiftHom : octonionLiftSubgroup K →* Model .G2 K :=
  faithfulConjugationLiftHom (faithfulMatrixHom8 K) (gamma K) (geckRepresentation K)
    (gamma_injective K) (geckRepresentation_injective K)

def liftedX (i : Fin 2) (t : K) : octonionLiftSubgroup K :=
  ⟨octonionSimpleRoot K (Fin.castAdd 2 i) t,
    ⟨⟨geckRepresentation K (modelX .G2 K i t), ⟨modelX .G2 K i t, rfl⟩⟩,
      octonion_X_compatible K i t⟩⟩

def liftedY (i : Fin 2) (t : K) : octonionLiftSubgroup K :=
  ⟨octonionSimpleRoot K (Fin.natAdd 2 i) t,
    ⟨⟨geckRepresentation K (modelY .G2 K i t), ⟨modelY .G2 K i t, rfl⟩⟩,
      octonion_Y_compatible K i t⟩⟩

theorem octonionLiftHom_X (i : Fin 2) (t : K) :
    octonionLiftHom K (liftedX K i t) = modelX .G2 K i t :=
  faithfulConjugationLiftHom_eq (faithfulMatrixHom8 K) (gamma K) (geckRepresentation K)
    (gamma_injective K) (geckRepresentation_injective K) _ _ (octonion_X_compatible K i t)

theorem octonionLiftHom_Y (i : Fin 2) (t : K) :
    octonionLiftHom K (liftedY K i t) = modelY .G2 K i t :=
  faithfulConjugationLiftHom_eq (faithfulMatrixHom8 K) (gamma K) (geckRepresentation K)
    (gamma_injective K) (geckRepresentation_injective K) _ _ (octonion_Y_compatible K i t)

theorem octonionLiftHom_surjective : Function.Surjective (octonionLiftHom K) := by
  apply adjointHom_surjective_of_root_lifts
    (rootDatum .G2).pairing (rootDatum .G2).base K (octonionLiftHom K)
    (fun i t => liftedX K ((rootDatum .G2).indexEquiv.symm i) t)
    (fun i t => liftedY K ((rootDatum .G2).indexEquiv.symm i) t)
  · intro i t
    obtain ⟨k, rfl⟩ := (rootDatum .G2).indexEquiv.surjective i
    simpa only [Equiv.symm_apply_apply, modelX] using octonionLiftHom_X K k t
  · intro i t
    obtain ⟨k, rfl⟩ := (rootDatum .G2).indexEquiv.surjective i
    simpa only [Equiv.symm_apply_apply, modelY] using octonionLiftHom_Y K k t

end Atlas.Chevalley.Comparison.G2

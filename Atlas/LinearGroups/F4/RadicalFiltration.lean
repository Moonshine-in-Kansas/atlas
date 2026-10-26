import Atlas.LinearGroups.F4.Radical

/-! The actual radical has an exact central additive seven-by-eight filtration.
No assertion about its being the full point-stabilizer kernel is made here. -/
noncomputable section
namespace Atlas.F4
open Atlas.GroupTheory
variable {F : Type*} [Field F]

def radicalParameterEquiv : RadicalParameters F ≃* radicalSubgroup (F:=F) :=
  MonoidHom.ofInjective (f:=radicalHom) radicalElement_injective

attribute [local irreducible] radicalParameterEquiv

def radicalEightProjection : radicalSubgroup (F:=F) →* Multiplicative (Fin 8→F) :=
  (BilinearExtension.project (radicalCocycle (F:=F))).comp (radicalParameterEquiv (F:=F)).symm.toMonoidHom

def radicalSevenEmbedding : Multiplicative (Fin 7→F) →* radicalSubgroup (F:=F) :=
  (radicalParameterEquiv (F:=F)).toMonoidHom.comp (BilinearExtension.centralEmbedding (radicalCocycle (F:=F)))

theorem radicalSevenEmbedding_injective :
    Function.Injective (radicalSevenEmbedding (F:=F)) :=
  (radicalParameterEquiv (F:=F)).injective.comp (BilinearExtension.centralEmbedding_injective _)

theorem radicalEightProjection_surjective :
    Function.Surjective (radicalEightProjection (F:=F)) :=
  (BilinearExtension.project_surjective _).comp (radicalParameterEquiv (F:=F)).symm.surjective

theorem radicalSeven_central (z : Multiplicative (Fin 7→F)) (g : radicalSubgroup (F:=F)) :
    Commute (radicalSevenEmbedding z) g := by
  obtain ⟨p,rfl⟩ := (radicalParameterEquiv (F:=F)).surjective g
  exact (BilinearExtension.centralEmbedding_commute (radicalCocycle (F:=F)) z p).map
    (radicalParameterEquiv (F:=F)).toMonoidHom

theorem radical_filtration_exact :
    (radicalEightProjection (F:=F)).ker=(radicalSevenEmbedding (F:=F)).range := by
  ext g
  constructor
  · intro hg
    have hp : (radicalParameterEquiv (F:=F)).symm g∈(BilinearExtension.project (radicalCocycle (F:=F))).ker := hg
    rw [BilinearExtension.ker_project_eq_range] at hp
    obtain ⟨z,hz⟩ := hp
    refine ⟨z,?_⟩
    change (radicalParameterEquiv (F:=F)) (BilinearExtension.centralEmbedding (radicalCocycle (F:=F)) z)=g
    rw [hz,(radicalParameterEquiv (F:=F)).apply_symm_apply]
  · rintro ⟨z,rfl⟩
    change BilinearExtension.project (radicalCocycle (F:=F))
      ((radicalParameterEquiv (F:=F)).symm ((radicalParameterEquiv (F:=F))
        (BilinearExtension.centralEmbedding (radicalCocycle (F:=F)) z)))=1
    rw [(radicalParameterEquiv (F:=F)).symm_apply_apply]
    rfl

end Atlas.F4

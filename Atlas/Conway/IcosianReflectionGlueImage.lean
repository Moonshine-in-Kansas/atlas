import Atlas.Conway.IcosianReflectionSignKernel
import Atlas.Codes.IcosianGlueGeneration

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes

def icosianReflectionMonomialSubgroup : Subgroup icosianLiftedMonomial :=
  icosianReflectionGroup.comap icosianMonomialToHermitian

def icosianLiftedReduction : icosianLiftedMonomial →* IcosianGlueMonomialGroup GoldenFour :=
  icosianMonomialReduction.comp icosianLiftedMonomial.subtype

def icosianReflectionGlueImage : Subgroup (IcosianGlueMonomialGroup GoldenFour) :=
  icosianReflectionMonomialSubgroup.map icosianLiftedReduction

theorem icosianLiftedReduction_kernel_le_reflections :
    icosianLiftedReduction.ker≤ icosianReflectionMonomialSubgroup := by
  intro g hg
  exact icosianMonomial_kernel_mem_reflections g hg

theorem icosianReflectionGlueImage_le :
    icosianReflectionGlueImage≤ icosianGlueMonomialStabilizer GoldenFour := by
  rintro g ⟨x,hx,rfl⟩
  exact x.property

/-- The already verified sign kernel reduces full frame generation to the
complete small finite gluing stabilizer. -/
theorem icosianFrame_le_reflections_of_glue
    (h : icosianGlueMonomialStabilizer GoldenFour≤ icosianReflectionGlueImage) :
    icosianCoordinateFrameStabilizer≤ icosianReflectionGroup := by
  rw [← icosianMonomial_range_eq_frameStabilizer]
  rintro f ⟨g,rfl⟩
  have hm : icosianLiftedReduction g∈icosianReflectionGlueImage := h g.property
  have hc : g∈icosianReflectionGlueImage.comap icosianLiftedReduction := hm
  change g∈(icosianReflectionMonomialSubgroup.map icosianLiftedReduction).comap
    icosianLiftedReduction at hc
  rw [Subgroup.comap_map_eq_self icosianLiftedReduction_kernel_le_reflections] at hc
  exact hc

end Atlas.Conway

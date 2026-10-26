import Atlas.LinearGroups.F4.ParabolicMarkedPoint
import Atlas.LinearGroups.F4.ShortWeylTorus
import Atlas.LinearGroups.F4.ParameterSubgroups

noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

theorem parabolicVector_eq_basis :
    parabolicVector (F:=F)=basisVector (.inr (2,0)) := by
  apply Prod.ext
  · ext i; fin_cases i <;> simp [parabolicVector,basisVector]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [parabolicVector,basisVector]

theorem diagonalTorus_parabolicVector (t : TorusParameters F) :
    (diagonalTorus t).val parabolicVector =
      (weightCharacter (albertWeightCoefficients (.inr (2,0))) t : F) • parabolicVector := by
  change torusEquiv t parabolicVector = _
  rw [parabolicVector_eq_basis,torusEquiv_basis]

theorem diagonalTorus_mem_parabolicPointStabilizer (t : TorusParameters F) :
    diagonalTorus t∈parabolicPointStabilizer := by
  apply (mem_parabolicPointStabilizer_iff _).mpr
  exact ⟨weightCharacter (albertWeightCoefficients (.inr (2,0))) t,
    diagonalTorus_parabolicVector t⟩

theorem torusSubgroup_le_parabolicPointStabilizer :
    torusSubgroup (F:=F) ≤ parabolicPointStabilizer := by
  rintro g ⟨t,rfl⟩
  exact diagonalTorus_mem_parabolicPointStabilizer t

end Atlas.F4

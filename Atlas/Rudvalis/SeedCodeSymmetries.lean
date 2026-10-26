import Atlas.Rudvalis.SeedMonomials
import Atlas.Rudvalis.MonomialSeedCriterion

/-! The original defining P, I, rho and sigma are actual signed-code automorphisms. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem rudvalisUnitMonomial_mem (u : Fin 8) : rudvalisUnitMonomial u∈codeGroup := by
  apply monomial_mem_codeGroup_of_seeds
  intro t
  rw [rudvalisUnitMonomial_seed]
  split
  · exact quaternaryCode.neg_mem (quaternaryCode_seed _)
  · exact quaternaryCode_seed _

theorem rudvalisPMonomial_mem : rudvalisPMonomial∈codeGroup := by
  apply monomial_mem_codeGroup_of_seeds
  intro t
  rw [rudvalisPMonomial_seed]
  exact quaternaryCode_seed _

noncomputable def codeP : codeGroup := ⟨rudvalisPMonomial,rudvalisPMonomial_mem⟩
noncomputable def codeI : codeGroup := ⟨rudvalisUnitMonomial 4,rudvalisUnitMonomial_mem 4⟩
noncomputable def codeRho : codeGroup := ⟨rudvalisUnitMonomial 1,rudvalisUnitMonomial_mem 1⟩
noncomputable def codeSigma : codeGroup := ⟨rudvalisUnitMonomial 2,rudvalisUnitMonomial_mem 2⟩

theorem codeP_preserves (w : QuaternaryWord) :
    w∈quaternaryCode ↔ monomialHom codeP.val w∈quaternaryCode := codeP.prop w

theorem codeI_preserves (w : QuaternaryWord) :
    w∈quaternaryCode ↔ monomialHom codeI.val w∈quaternaryCode := codeI.prop w

theorem codeRho_preserves (w : QuaternaryWord) :
    w∈quaternaryCode ↔ monomialHom codeRho.val w∈quaternaryCode := codeRho.prop w

theorem codeSigma_preserves (w : QuaternaryWord) :
    w∈quaternaryCode ↔ monomialHom codeSigma.val w∈quaternaryCode := codeSigma.prop w

end Atlas.Rudvalis

import Atlas.Conway.EisensteinMonomialNormPatterns

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

theorem eisensteinSignIntegral (x : EisensteinLattice) :
    eisensteinIntegralAction eisensteinSignIsometry x = -x := by
  apply Subtype.ext
  apply eisensteinCoordinateEmbedding_injective
  rw [eisensteinIntegralAction_agrees]
  change -eisensteinCoordinateEmbedding x.val=eisensteinCoordinateEmbedding (-x.val)
  rw [map_neg]

theorem eisensteinSignShell_class (x : EisensteinShell 6) :
    eisensteinClass (eisensteinShellAction eisensteinSignIsometry 6 x).val =
      -eisensteinClass x.val := by
  change eisensteinClass (eisensteinIntegralAction eisensteinSignIsometry x.val)=_
  rw [eisensteinSignIntegral,map_neg]

theorem eisensteinSignShell_normCount (x : EisensteinShell 6) (n : ℤ) :
    eisensteinNormCount (eisensteinShellAction eisensteinSignIsometry 6 x) n =
      eisensteinNormCount x n := by
  have he : eisensteinMonomialParameterIsometry (true,0,1)=eisensteinSignIsometry := by
    simp [eisensteinMonomialParameterIsometry]
  simpa only [he] using eisensteinMonomialNormCount (true,0,1) x n

end Atlas.Conway

import Atlas.Tits.MonomialSmallQuotient
import Atlas.Rudvalis.ProjectiveFrameFiltration

/-! The actual projective point-fixing row kernel, as the image of the
row-trivial code point stabilizer under the inherited scalar projection. -/

namespace Atlas.Tits
open Atlas.Rudvalis

noncomputable def monomialPointRowKernel : Subgroup monomialPointGroup :=
  codeReferenceRowHom.ker.map codePointToMonomial

theorem point_scalar_kernel_le_row_kernel :
    codePointToMonomial.ker ≤ codeReferenceRowHom.ker := by
  intro g hg
  have he : codePointHom g = 1 := congrArg Subtype.val
    (show codePointToMonomial g = 1 from hg)
  have hu : g.val ∈ GaussianUnits := (codePointHom_kernel g).mp he
  change codeReferenceRowHom g = 1
  apply Subtype.ext
  exact gaussianUnits_le_codeRowKernel hu

theorem monomialPointRowKernel_index : monomialPointRowKernel.index = 24 := by
  have hs : Function.Surjective codePointToMonomial := codePointHom.rangeRestrict_surjective
  rw [monomialPointRowKernel,
    Subgroup.index_map_eq _ hs
      point_scalar_kernel_le_row_kernel,Subgroup.index_ker,
    codeReferenceRowHom.range_eq_top_of_surjective codeReferenceRowHom_surjective,
    Subgroup.card_top,localRowStabilizer_card]

theorem monomialPointRowKernel_card : Nat.card monomialPointRowKernel = 512 := by
  have h := monomialPointRowKernel.card_mul_index
  rw [monomialPointRowKernel_index,cardMonomialPointGroup] at h
  omega

end Atlas.Tits

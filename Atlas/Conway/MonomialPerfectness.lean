import Atlas.Conway.MonomialOctadCommutators
import Atlas.Conway.MonomialCentralQuotient

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def monomialDerivedCode : Submodule Bit golay where
  carrier := {c | (SemidirectProduct.inl (Multiplicative.ofAdd c) : GolayMonomialGroup) ∈
    commutator GolayMonomialGroup}
  zero_mem' := by
    change SemidirectProduct.inl 1 ∈ commutator GolayMonomialGroup
    rw [map_one]
    exact Subgroup.one_mem _
  add_mem' {c d} hc hd := by
    change (SemidirectProduct.inl (Multiplicative.ofAdd c * Multiplicative.ofAdd d) : GolayMonomialGroup) ∈ commutator GolayMonomialGroup
    rw [map_mul]
    exact Subgroup.mul_mem _ hc hd
  smul_mem' b c hc := by
    rcases bit_cases b with rfl | rfl
    · simpa only [zero_smul] using (show (0 : golay) ∈
        {c | (SemidirectProduct.inl (Multiplicative.ofAdd c) : GolayMonomialGroup) ∈
          commutator GolayMonomialGroup} from by
            change SemidirectProduct.inl 1 ∈ commutator GolayMonomialGroup
            rw [map_one]; exact Subgroup.one_mem _)
    · simpa only [one_smul] using hc

theorem monomialDerivedCode_eq_top : monomialDerivedCode = ⊤ := by
  have hmap : golay ≤ monomialDerivedCode.map golay.subtype := by
    conv_lhs => rw [← octads_span]
    apply Submodule.span_le.mpr
    intro w hw
    have hO : support w ∈ octads := (octads_mem _).mpr ⟨⟨w,hw.1⟩,hw.2,rfl⟩
    have he : octadCode (support w) hO = (⟨w,hw.1⟩ : golay) :=
      Subtype.ext (binarySupportEquiv.left_inv w)
    refine ⟨⟨w,hw.1⟩,?_,rfl⟩
    change (SemidirectProduct.inl (Multiplicative.ofAdd (⟨w,hw.1⟩ : golay)) :
      GolayMonomialGroup) ∈ commutator GolayMonomialGroup
    rw [← he]
    exact octad_sign_mem_commutator _ hO
  apply top_unique
  intro c _
  obtain ⟨d,hd,he⟩ := hmap c.prop
  have hdc : d = c := Subtype.ext he
  rwa [← hdc]

theorem golay_sign_mem_commutator (c : golay) :
    (SemidirectProduct.inl (Multiplicative.ofAdd c) : GolayMonomialGroup) ∈
      commutator GolayMonomialGroup := by
  change c ∈ monomialDerivedCode
  rw [monomialDerivedCode_eq_top]
  trivial

theorem mathieu24_perfect : Group.IsPerfect Mathieu24CodeModel := by
  letI := mathieu24_simple
  exact Atlas.GroupTheory.nonabelian_simple_perfect _ mathieu24_noncommuting_pair

theorem monomial_permutation_mem_commutator (g : Mathieu24CodeModel) :
    (SemidirectProduct.inr g : GolayMonomialGroup) ∈ commutator GolayMonomialGroup := by
  letI := mathieu24_perfect
  let f : Mathieu24CodeModel →* GolayMonomialGroup := SemidirectProduct.inr
  have hle : (commutator Mathieu24CodeModel).map f ≤ commutator GolayMonomialGroup :=
    (map_commutator_eq _ f).le.trans (Subgroup.commutator_mono le_top le_top)
  apply hle
  exact ⟨g,Group.IsPerfect.mem_commutator,rfl⟩

theorem golayMonomialGroup_perfect : Group.IsPerfect GolayMonomialGroup := by
  constructor
  apply top_unique
  intro g _
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  exact Subgroup.mul_mem _ (golay_sign_mem_commutator g.left.toAdd)
    (monomial_permutation_mem_commutator g.right)

theorem monomialSubgroup_perfect : Group.IsPerfect monomialSubgroup := by
  letI := golayMonomialGroup_perfect
  exact Group.IsPerfect.ofSurjective (f := monomialSubgroupEquiv.toMonoidHom)
    monomialSubgroupEquiv.surjective

theorem quotientMonomialSubgroup_perfect : Group.IsPerfect quotientMonomialSubgroup := by
  letI := golayMonomialGroup_perfect
  exact Group.IsPerfect.range quotientMonomialEmbedding

end Atlas.Conway

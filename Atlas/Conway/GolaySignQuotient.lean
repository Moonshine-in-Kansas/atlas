import Atlas.Conway.MonomialCentralQuotient

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

/-- The additive all-ones Golay word, in multiplicative notation. -/
def golayOneWord : Multiplicative golay :=
  Multiplicative.ofAdd ⟨allOnes,C0_le_golay allOnes_mem_C0⟩

def golayOneSubgroup : Subgroup (Multiplicative golay) := Subgroup.zpowers golayOneWord

abbrev GolaySignQuotient := Multiplicative golay ⧸ golayOneSubgroup

def golaySignProjection : Multiplicative golay →* GolaySignQuotient :=
  QuotientGroup.mk' golayOneSubgroup

theorem golayPermutation_fixes_oneWord (g : Mathieu24CodeModel) :
    golayPermutationAction g golayOneWord = golayOneWord := by
  rfl

theorem golayOneSubgroup_invariant (g : Mathieu24CodeModel) :
    golayOneSubgroup.map (golayPermutationAction g).toMonoidHom = golayOneSubgroup := by
  rw [golayOneSubgroup,MonoidHom.map_zpowers]
  rfl

def golaySignQuotientAction : Mathieu24CodeModel →* MulAut GolaySignQuotient where
  toFun g := QuotientGroup.congr _ _ (golayPermutationAction g) (golayOneSubgroup_invariant g)
  map_one' := by
    apply MulEquiv.ext; intro c
    obtain ⟨c,rfl⟩ := QuotientGroup.mk'_surjective golayOneSubgroup c
    change golaySignProjection (golayPermutationAction 1 c) = golaySignProjection c
    rw [map_one]; rfl
  map_mul' g h := by
    apply MulEquiv.ext; intro c
    obtain ⟨c,rfl⟩ := QuotientGroup.mk'_surjective golayOneSubgroup c
    change golaySignProjection (golayPermutationAction (g*h) c) =
      golaySignProjection (golayPermutationAction g (golayPermutationAction h c))
    rw [map_mul]; rfl

theorem golaySignQuotientAction_compatible (g : Mathieu24CodeModel) (c : Multiplicative golay) :
    golaySignQuotientAction g (golaySignProjection c) =
      golaySignProjection (golayPermutationAction g c) := rfl

abbrev GolayQuotientMonomialGroup := GolaySignQuotient ⋊[golaySignQuotientAction] Mathieu24CodeModel

def monomialSignQuotientProjection : GolayMonomialGroup →* GolayQuotientMonomialGroup :=
  SemidirectProduct.map golaySignProjection (MonoidHom.id _) (by intro g; rfl)

theorem monomialSignQuotientProjection_surjective :
    Function.Surjective monomialSignQuotientProjection := by
  intro m
  obtain ⟨c,hc⟩ := QuotientGroup.mk'_surjective golayOneSubgroup m.left
  refine ⟨⟨c,m.right⟩,?_⟩
  apply SemidirectProduct.ext
  · exact hc
  · rfl

theorem monomialSignQuotientProjection_kernel :
    monomialSignQuotientProjection.ker = quotientMonomialEmbedding.ker := by
  rw [quotientMonomialEmbedding_kernel]
  have he : golayOneSubgroup.map (SemidirectProduct.inl : Multiplicative golay →* GolayMonomialGroup) =
      Subgroup.zpowers monomialCentralElement := by
    exact MonoidHom.map_zpowers _ _
  rw [← he]
  ext m
  constructor
  · intro hm
    have hl := congrArg SemidirectProduct.left (MonoidHom.mem_ker.mp hm)
    have hr := congrArg SemidirectProduct.right (MonoidHom.mem_ker.mp hm)
    change golaySignProjection m.left = 1 at hl
    change m.right = 1 at hr
    refine ⟨m.left,?_,?_⟩
    · exact (QuotientGroup.eq_one_iff _).mp hl
    · apply SemidirectProduct.ext
      · rfl
      · exact hr.symm
  · rintro ⟨c,hc,rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply SemidirectProduct.ext
    · exact (QuotientGroup.eq_one_iff _).mpr hc
    · rfl

end Atlas.Conway

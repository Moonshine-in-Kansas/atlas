import Atlas.Rudvalis.CanonicalDozens
import Atlas.Combinatorics.BiregularIncidence

namespace Atlas.Rudvalis

abbrev CanonicalFramesThroughCross (x : MinimalCross) := {F : canonicalBases // x∈F.val}
abbrev CanonicalFramesThroughCouple (c : Set MinimalCross) := {F : canonicalBases // c⊆F.val}

noncomputable def canonicalFramesEquiv (g : gaussianLatticeGroup) : Equiv.Perm canonicalBases :=
  Equiv.subtypeEquiv (gaussianConfigurationEquiv g) (fun F=>(canonicalBases_gaussianImage g F).symm)

noncomputable def canonicalFramesThroughCrossEquiv (g : gaussianLatticeGroup) (x : MinimalCross) :
    CanonicalFramesThroughCross x ≃ CanonicalFramesThroughCross (g • x) :=
  Equiv.subtypeEquiv (canonicalFramesEquiv g) (fun F=>(gaussianImage_mem g F.val x).symm)

noncomputable def canonicalFramesThroughCoupleEquiv (g : gaussianLatticeGroup) (c : Set MinimalCross) :
    CanonicalFramesThroughCouple c ≃ CanonicalFramesThroughCouple (gaussianImage g c) :=
  Equiv.subtypeEquiv (canonicalFramesEquiv g) (fun F=>(gaussianImage_subset_iff g c F.val).symm)

theorem canonicalFramesThroughCross_card_eq (x y : MinimalCross) :
    Nat.card (CanonicalFramesThroughCross x)=Nat.card (CanonicalFramesThroughCross y) := by
  let := rudvalis_generated_cross_transitive
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq generatedGaussianGroup x y
  rw [←hg]
  exact Nat.card_congr (canonicalFramesThroughCrossEquiv g.val x)

theorem canonicalFramesThroughCouple_card_reference (c : Set MinimalCross) (hc : IsCouple c) :
    Nat.card (CanonicalFramesThroughCouple c)=Nat.card (CanonicalFramesThroughCouple referenceCouple) := by
  obtain ⟨g,rfl⟩ := generated_couple_transport c hc
  exact (Nat.card_congr (canonicalFramesThroughCoupleEquiv g.val referenceCouple)).symm

theorem canonicalFramesThroughCross_incidence (x : MinimalCross) :
    Nat.card MinimalCross*Nat.card (CanonicalFramesThroughCross x)=Nat.card canonicalBases*28 := by
  apply Atlas.Combinatorics.uniform_incidence_card (fun y : MinimalCross=>fun F : canonicalBases=>y∈F.val)
  · intro y
    exact canonicalFramesThroughCross_card_eq y x
  · intro F
    exact (canonicalFrame_isFrame F.val F.prop).1

end Atlas.Rudvalis

import Atlas.Fischer.CubicCommonNeighborPairs

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The source common-neighbor distribution for every actual pair of Golay
octads meeting in four points. Each number is derived through the retained
sextet marking and the complete source column parametrization. -/
theorem cubicCommonNeighbor_distribution (D F : Octad) (hDF : (D.val ∩ F.val).card=4) :
    cubicCommonNeighborCount D F 0=1 ∧ cubicCommonNeighborCount D F 2=72 ∧
      cubicCommonNeighborCount D F 3=64 ∧ cubicCommonNeighborCount D F 4=3 := by
  obtain ⟨g,i,j,k,hij,hik,hjk,hD,hF⟩ := cubicCommonNeighbor_pair_normalize D F hDF
  have hI : hexIndexEquiv i ≠ hexIndexEquiv j := fun h => hij (hexIndexEquiv.injective h)
  have hJ : hexIndexEquiv i ≠ hexIndexEquiv k := fun h => hik (hexIndexEquiv.injective h)
  have hK : hexIndexEquiv j ≠ hexIndexEquiv k := fun h => hjk (hexIndexEquiv.injective h)
  have he (u : ℕ) : cubicCommonNeighborCount D F u=
      Nat.card (CubicSourceCommonNeighbors (hexIndexEquiv i) (hexIndexEquiv j) (hexIndexEquiv k) u) :=
    (cubicCommonNeighborCount_invariant g D F u).trans
      (cubicCommonNeighbor_source_card (g • D) (g • F) i j k hij hik hjk hD hF u).symm
  simp_rw [he]
  exact ⟨cubicSourceCommonZero_card _ _ _ hI hJ hK,
    cubicSourceCommonTwo_card _ _ _ hI hJ hK,
    cubicSourceCommonThree_card _ _ _ hI hJ hK,
    cubicSourceCommonFour_card _ _ _ hI hJ hK⟩

end Atlas.Fischer

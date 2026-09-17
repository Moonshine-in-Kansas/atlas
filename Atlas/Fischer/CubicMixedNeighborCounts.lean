import Atlas.Fischer.CubicMixedNeighborProfiles
import Atlas.Fischer.CubicCommonNeighborDisjoint

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

abbrev CubicPairIntersectionFibre (D F : Octad) (a b : ℕ) :=
  {G : Octad // (D.val ∩ G.val).card = a ∧ (F.val ∩ G.val).card = b}

def cubicPairIntersectionPermute (g : Mathieu24CodeModel) (D F : Octad) (a b : ℕ) :
    CubicPairIntersectionFibre D F a b ≃ CubicPairIntersectionFibre (g • D) (g • F) a b where
  toFun G := ⟨g • G.val,by simpa only [cubicCommonNeighbor_pair_card] using G.property⟩
  invFun G := ⟨g⁻¹ • G.val,by
    have hp := cubicCommonNeighbor_pair_card g⁻¹ (g • D) G.val
    have hq := cubicCommonNeighbor_pair_card g⁻¹ (g • F) G.val
    simp only [inv_smul_smul] at hp hq
    exact ⟨hp.trans G.property.1,hq.trans G.property.2⟩⟩
  left_inv G := by apply Subtype.ext; exact inv_smul_smul g G.val
  right_inv G := by apply Subtype.ext; exact smul_inv_smul g G.val

theorem cubicPairIntersection_source_card (D F : Octad) (i j k : HexIndex)
    (hij : i ≠ j) (hik : i ≠ k)
    (hD : D.val = tetrad i ∪ tetrad j) (hF : F.val = tetrad i ∪ tetrad k) (a b : ℕ) :
    Nat.card (CubicSourcePairNeighbors (hexIndexEquiv i) (hexIndexEquiv j) (hexIndexEquiv k) a b) =
      Nat.card (CubicPairIntersectionFibre D F a b) := by
  apply Nat.card_congr
  apply Equiv.subtypeEquiv countingSourceOctadEquiv
  intro t
  change _ ↔ (D.val ∩ (countingSourceOctadEquiv t).val).card = a ∧
    (F.val ∩ (countingSourceOctadEquiv t).val).card = b
  rw [hD,hF,cubicCommonNeighbor_two_column_card _ i j hij,
    cubicCommonNeighbor_two_column_card _ i k hik]
  simp only [cubicCommonNeighbor_column_card]

theorem cubicPairIntersection_four_mixed (D F : Octad) (hDF : (D.val ∩ F.val).card = 4) :
    Nat.card (CubicPairIntersectionFibre D F 0 4) = 3 ∧
      Nat.card (CubicPairIntersectionFibre D F 0 0) = 3 := by
  obtain ⟨g,i,j,k,hij,hik,hjk,hD,hF⟩ := cubicCommonNeighbor_pair_normalize D F hDF
  have hI : hexIndexEquiv i ≠ hexIndexEquiv j := fun h => hij (hexIndexEquiv.injective h)
  have hJ : hexIndexEquiv i ≠ hexIndexEquiv k := fun h => hik (hexIndexEquiv.injective h)
  have hK : hexIndexEquiv j ≠ hexIndexEquiv k := fun h => hjk (hexIndexEquiv.injective h)
  have he (a b : ℕ) : Nat.card (CubicPairIntersectionFibre D F a b) =
      Nat.card (CubicSourcePairNeighbors (hexIndexEquiv i) (hexIndexEquiv j) (hexIndexEquiv k) a b) :=
    (Nat.card_congr (cubicPairIntersectionPermute g D F a b)).trans
      (cubicPairIntersection_source_card (g • D) (g • F) i j k hij hik hD hF a b).symm
  rw [he 0 4,he 0 0]
  exact ⟨cubicSourceMixed_card _ _ _ hI hJ hK,cubicSourceBothZero_card _ _ _ hI hJ hK⟩

def cubicPairIntersectionSwap (D F : Octad) (a b : ℕ) :
    CubicPairIntersectionFibre D F a b ≃ CubicPairIntersectionFibre F D b a where
  toFun G := ⟨G.val,G.property.2,G.property.1⟩
  invFun G := ⟨G.val,G.property.2,G.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Atlas.Fischer

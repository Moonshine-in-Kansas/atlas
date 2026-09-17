import Atlas.Conway.OrthogonalLineStabilizer

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
set_option maxRecDepth 10000

def distinguishedOrthogonalLine (i j : Omega) (hij : i ≠ j) :
    OrthogonalMinimumLines (minimumPairPlus i j) :=
  ⟨antipodalLine (minimumPairMinus i j),minimumPairMinus i j,
    ⟨minimumPairMinus_norm i j hij,minimumPair_orthogonal i j hij⟩,rfl⟩

theorem distinguishedOrthogonalLine_stabilizer (i j : Omega) (hij : i ≠ j) :
    MulAction.stabilizer (fullVectorStabilizer (minimumPairPlus i j))
      (distinguishedOrthogonalLine i j hij) = orthogonalLineStabilizer i j := by
  ext g
  exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩

theorem orthogonalLineStabilizer_order (i j : Omega) (hij : i ≠ j) :
    Nat.card (orthogonalLineStabilizer i j) = 908328960 := by
  letI := orthogonalMinimumLines_pretransitive i j hij
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    (fullVectorStabilizer (minimumPairPlus i j)) (distinguishedOrthogonalLine i j hij))
  rw [Nat.card_prod,MulAction.orbit_eq_univ,Nat.card_congr (Equiv.Set.univ _),
    orthogonalMinimumLines_card i j hij,distinguishedOrthogonalLine_stabilizer] at h
  have ho := minimum_vector_stabilizer_order
    (⟨minimumPairPlus i j,minimumPairPlus_norm i j hij⟩ : LeechShell 4)
  change Nat.card (fullVectorStabilizer (minimumPairPlus i j)) = 42305421312000 at ho
  rw [ho] at h
  omega

end Atlas.Conway

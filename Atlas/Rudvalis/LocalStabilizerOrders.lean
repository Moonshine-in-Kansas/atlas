import Atlas.Rudvalis.FullPointStabilizer
import Atlas.Rudvalis.GaussianGroupOrder

namespace Atlas.Rudvalis

theorem full_gaussian_cross_transitive : MulAction.IsPretransitive gaussianLatticeGroup MinimalCross := by
  let := rudvalis_generated_cross_transitive
  constructor
  intro a b
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq generatedGaussianGroup a b
  exact ⟨g.val,hg⟩

theorem full_gaussian_orthogonal_pairs_transitive :
    MulAction.IsPretransitive gaussianLatticeGroup OrthogonalPairs := by
  let := rudvalis_generated_orthogonal_pairs_transitive
  constructor
  intro a b
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq generatedGaussianGroup a b
  exact ⟨g.val,hg⟩

theorem full_point_stabilizer_card_equation (x : MinimalCross) :
    4060*Nat.card (MulAction.stabilizer gaussianLatticeGroup x)=Nat.card gaussianLatticeGroup := by
  let := full_gaussian_cross_transitive
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup gaussianLatticeGroup x)
  rw [Nat.card_prod,MulAction.orbit_eq_univ,Nat.card_univ,rudvalisLattice_minimal_cross_card] at h
  exact h

noncomputable def referenceCoupleOrdered : OrthogonalPairs :=
  ⟨(localReferenceCross,referenceSecondCross),reference_crosses_orthogonal⟩

theorem referenceCoupleOrdered_stabilizer :
    MulAction.stabilizer gaussianLatticeGroup referenceCoupleOrdered=coupleFusionGroup := by
  rw [coupleFusionGroup_eq_pair_stabilizer]
  ext g
  change (g • referenceCoupleOrdered=referenceCoupleOrdered) ↔
    (g • localReferenceCross=localReferenceCross ∧ g • referenceSecondCross=referenceSecondCross)
  rw [Subtype.ext_iff]
  exact Prod.ext_iff

theorem full_pair_stabilizer_card_equation :
    7125300*Nat.card coupleFusionGroup=Nat.card gaussianLatticeGroup := by
  let := full_gaussian_orthogonal_pairs_transitive
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup gaussianLatticeGroup referenceCoupleOrdered)
  rw [Nat.card_prod,MulAction.orbit_eq_univ,Nat.card_univ,rudvalis_ordered_orthogonal_pairs_card,
    referenceCoupleOrdered_stabilizer] at h
  exact h

/-- The stabilizer of every actual minimal cross has this exact order. -/
theorem full_point_stabilizer_order (x : MinimalCross) :
    Nat.card (MulAction.stabilizer gaussianLatticeGroup x)=143769600 := by
  have h := full_point_stabilizer_card_equation x
  rw [full_gaussian_order] at h
  omega

theorem localFusionGroup_order : Nat.card localFusionGroup=143769600 := by
  rw [localFusionGroup_eq_point_stabilizer]
  exact full_point_stabilizer_order _

/-- The concrete group A is the full pointwise reference-couple stabilizer. -/
theorem coupleFusionGroup_order : Nat.card coupleFusionGroup=81920 := by
  have h := full_pair_stabilizer_card_equation
  rw [full_gaussian_order] at h
  omega

/-- The stabilizer of every actual ordered orthogonal pair has this exact order. -/
theorem full_orthogonal_pair_stabilizer_order (z : OrthogonalPairs) :
    Nat.card (MulAction.stabilizer gaussianLatticeGroup z)=81920 := by
  let := full_gaussian_orthogonal_pairs_transitive
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup gaussianLatticeGroup z)
  rw [Nat.card_prod,MulAction.orbit_eq_univ,Nat.card_univ,rudvalis_ordered_orthogonal_pairs_card,
    full_gaussian_order] at h
  omega

theorem full_pointwise_couple_stabilizer_order (x y : MinimalCross)
    (hxy : CrossOrthogonal x y) :
    Nat.card (MulAction.stabilizer gaussianLatticeGroup x ⊓
      MulAction.stabilizer gaussianLatticeGroup y : Subgroup gaussianLatticeGroup)=81920 := by
  have he : MulAction.stabilizer gaussianLatticeGroup (⟨(x,y),hxy⟩ : OrthogonalPairs)=
      MulAction.stabilizer gaussianLatticeGroup x ⊓ MulAction.stabilizer gaussianLatticeGroup y := by
    ext g
    change (g • (⟨(x,y),hxy⟩ : OrthogonalPairs)=(⟨(x,y),hxy⟩ : OrthogonalPairs)) ↔
      (g • x=x ∧ g • y=y)
    rw [Subtype.ext_iff]
    exact Prod.ext_iff
  rw [←he]
  exact full_orthogonal_pair_stabilizer_order _

end Atlas.Rudvalis


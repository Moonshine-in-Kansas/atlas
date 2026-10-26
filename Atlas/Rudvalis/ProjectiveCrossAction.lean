import Atlas.Rudvalis.ScalarQuotient
import Atlas.Rudvalis.LocalStabilizerOrders

namespace Atlas.Rudvalis

theorem gaussianUnits_cross_fix (u : GaussianUnits) (c : MinimalCross) : u.val • c=c := by
  induction c using Quotient.inductionOn with
  | h v => exact (minimalCross_eq_iff _ _).mpr ⟨u,rfl⟩

theorem gaussianScalarSubgroup_cross_kernel :
    gaussianScalarSubgroup ≤ (MulAction.toPermHom gaussianLatticeGroup MinimalCross).ker := by
  rintro g ⟨u,hu,rfl⟩
  apply Equiv.ext
  intro c
  change codeGaussianHom u • c=c
  rw [codeGaussianHom_cross]
  exact gaussianUnits_cross_fix ⟨u,hu⟩ c

noncomputable def rudvalisCrossHom : RudvalisGroup →* Equiv.Perm MinimalCross :=
  QuotientGroup.lift _ (MulAction.toPermHom gaussianLatticeGroup MinimalCross)
    gaussianScalarSubgroup_cross_kernel

noncomputable instance rudvalisCrossAction : MulAction RudvalisGroup MinimalCross :=
  MulAction.compHom _ rudvalisCrossHom

theorem rudvalisCrossAction_mk (g : gaussianLatticeGroup) (c : MinimalCross) :
    (QuotientGroup.mk g : RudvalisGroup) • c=g • c := rfl

theorem rudvalis_cross_pretransitive : MulAction.IsPretransitive RudvalisGroup MinimalCross := by
  let := full_gaussian_cross_transitive
  constructor
  intro a b
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq gaussianLatticeGroup a b
  exact ⟨QuotientGroup.mk g,hg⟩

theorem rudvalis_point_stabilizer_order (x : MinimalCross) :
    Nat.card (MulAction.stabilizer RudvalisGroup x)=35942400 := by
  let := rudvalis_cross_pretransitive
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup RudvalisGroup x)
  rw [Nat.card_prod,MulAction.orbit_eq_univ,Nat.card_univ,
    rudvalisLattice_minimal_cross_card,rudvalisGroup_order] at h
  omega

end Atlas.Rudvalis

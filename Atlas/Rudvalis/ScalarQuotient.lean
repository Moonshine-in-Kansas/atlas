import Atlas.Rudvalis.GaussianGroupOrder
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center

namespace Atlas.Rudvalis

noncomputable def gaussianScalarSubgroup : Subgroup gaussianLatticeGroup :=
  GaussianUnits.map codeGaussianHom

theorem gaussian_commute_I (g : gaussianLatticeGroup) : Commute g (codeGaussianHom codeI) := by
  change g*codeGaussianHom codeI=codeGaussianHom codeI*g
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact g.prop.2.2 v

theorem gaussianScalarSubgroup_le_center : gaussianScalarSubgroup≤Subgroup.center gaussianLatticeGroup := by
  rintro a ⟨u,hu,rfl⟩
  obtain ⟨k,hk⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [←hk,map_zpow]
  apply Subgroup.mem_center_iff.mpr
  intro g
  exact (gaussian_commute_I g).zpow_right k

instance gaussianScalarSubgroup_normal : gaussianScalarSubgroup.Normal :=
  ⟨fun a ha b=>by
    have h := Subgroup.mem_center_iff.mp (gaussianScalarSubgroup_le_center ha) b
    have he : b*a*b⁻¹=a := by rw [h,mul_assoc,mul_inv_cancel,mul_one]
    simpa only [he] using ha⟩

theorem gaussianScalarSubgroup_card : Nat.card gaussianScalarSubgroup=4 := by
  change Nat.card (GaussianUnits.map codeGaussianHom)=4
  rw [←Nat.card_congr (GaussianUnits.equivMapOfInjective codeGaussianHom codeGaussianHom_injective).toEquiv]
  exact gaussianUnits_card

theorem gaussianScalarSubgroup_eq_zpowers :
    gaussianScalarSubgroup=Subgroup.zpowers (codeGaussianHom codeI) :=
  codeGaussianHom.map_zpowers codeI

theorem gaussianUnits_le_center : GaussianUnits≤Subgroup.center codeGroup := by
  intro u hu
  apply Subgroup.mem_center_iff.mpr
  intro g
  exact codeGroup_commute_gaussianUnits g ⟨u,hu⟩

instance gaussianUnits_normal : GaussianUnits.Normal :=
  ⟨fun a ha b=>by
    have h := Subgroup.mem_center_iff.mp (gaussianUnits_le_center ha) b
    have he : b*a*b⁻¹=a := by rw [h,mul_assoc,mul_inv_cancel,mul_one]
    simpa only [he] using ha⟩

/-- The actual full Gaussian lattice group modulo its four scalar units. -/
noncomputable abbrev RudvalisGroup := gaussianLatticeGroup ⧸ gaussianScalarSubgroup

/-- The actual monomial frame group modulo those same scalar units. -/
noncomputable abbrev ProjectiveCodeGroup := codeGroup ⧸ GaussianUnits

theorem rudvalisGroup_order : Nat.card RudvalisGroup=145926144000 := by
  have h := gaussianScalarSubgroup.card_eq_card_quotient_mul_card_subgroup
  rw [full_gaussian_order,gaussianScalarSubgroup_card] at h
  change 583704576000=Nat.card RudvalisGroup*4 at h
  omega

theorem projectiveCodeGroup_order : Nat.card ProjectiveCodeGroup=344064 := by
  have h := GaussianUnits.card_eq_card_quotient_mul_card_subgroup
  rw [codeGroup_order,gaussianUnits_card] at h
  change 1376256=Nat.card ProjectiveCodeGroup*4 at h
  omega

end Atlas.Rudvalis

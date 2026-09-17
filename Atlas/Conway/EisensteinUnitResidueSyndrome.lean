import Atlas.Conway.EisensteinUnitResidueNormalization
import Atlas.Conway.EisensteinUnitResidueShortReferences
import Atlas.Conway.EisensteinTriadUnitParameters

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem eisensteinOneModThree_sum (x : EisensteinLattice) (a : EisensteinCoordinates)
    (ha : ∀ j, x.val j=1+3*a j) : eisensteinTheta ∣ 5+∑ j, a j := by
  have hm := eisensteinLeechModule_common_lift x.val x.property 1
    (fun j => by simpa using eisensteinOneModThree_residue x ⟨a,ha⟩ j)
  obtain ⟨_,_,_,d,hd⟩ := hm
  have hs : (∑ j, x.val j)=12+3*(∑ j, a j) := by
    simp_rw [ha]
    simp [Finset.sum_add_distrib,← Finset.mul_sum]
  rw [hs] at hd
  refine ⟨d,?_⟩
  apply eisenstein_theta_cancel
  apply eisenstein_theta_cancel
  linear_combination -hd+(5+(∑ j, a j)-eisensteinTheta*d)*eisensteinTheta_sq

theorem eisensteinOneModThree_affine_sum (x : EisensteinLattice) (a : EisensteinCoordinates)
    (ha : ∀ j, x.val j=1+3*a j) : ternaryWordSum (eisensteinWordResidue a)=1 := by
  have hh := (eisensteinResidue_eq_zero _).mpr (eisensteinOneModThree_sum x a ha)
  rw [map_add,map_sum] at hh
  change (2 : ZMod 3)+(∑ j, eisensteinResidue (a j))=0 at hh
  change (∑ j, eisensteinResidue (a j))=1
  exact (eq_neg_of_add_eq_zero_right hh).trans (by decide +kernel)

def eisensteinOneModThreeSyndrome (x : EisensteinLattice) (a : EisensteinCoordinates)
    (ha : ∀ j, x.val j=1+3*a j) : TernaryAffineSyndrome :=
  ⟨ternarySyndromeClass (eisensteinWordResidue a),eisensteinOneModThree_affine_sum x a ha⟩

end Atlas.Conway

import Atlas.LinearGroups.Chevalley.TwistedE6.DualMatrices
import Atlas.LinearGroups.Chevalley.TwistedE6.AdjointDiagram
import Atlas.LinearGroups.Chevalley.WeightCompanion

/-! The graph involution of the actual simultaneous adjoint and dual-minuscule
matrix group. The restriction is proved on its specified root generators. -/
noncomputable section
namespace Atlas.Chevalley.TwistedE6
open Classical E6Data Integral.Minuscule
local instance dualCompanionRootFintype : Fintype Root := Fintype.ofFinite Root
variable (R : Type*) [CommRing R]

abbrev DualCompanion :=
  WeightCompanion pairing base dualOrbits dualOrbits_closed dualOrbits_minuscule R

def dualAmbientDiagram : WeightCompanionAmbient pairing base dualOrbits R →*
    WeightCompanionAmbient pairing base dualOrbits R where
  toFun g := (adjointDiagram R g.1, dualBlocksDiagram R g.2)
  map_one' := Prod.ext (map_one _) (map_one _)
  map_mul' _g _h := Prod.ext (map_mul _ _ _) (map_mul _ _ _)

theorem dualAmbientDiagram_involutive : Function.Involutive (dualAmbientDiagram R) := by
  intro g
  exact Prod.ext (adjointDiagram_involutive R g.1) (dualBlocksDiagram_involutive R g.2)

theorem dualAmbientDiagram_X (i : base.support) (t : R) :
    dualAmbientDiagram R
      (weightCompanionRootX pairing base dualOrbits dualOrbits_closed dualOrbits_minuscule R i t) =
    weightCompanionRootX pairing base dualOrbits dualOrbits_closed dualOrbits_minuscule
      R (baseDiagram i) t := by
  apply Prod.ext
  · exact adjointDiagram_X R i t
  · funext a
    exact dualUnitsDiagram_root R a i (-1) (by decide) t

theorem dualAmbientDiagram_Y (i : base.support) (t : R) :
    dualAmbientDiagram R
      (weightCompanionRootY pairing base dualOrbits dualOrbits_closed dualOrbits_minuscule R i t) =
    weightCompanionRootY pairing base dualOrbits dualOrbits_closed dualOrbits_minuscule
      R (baseDiagram i) t := by
  apply Prod.ext
  · exact adjointDiagram_Y R i t
  · funext a
    exact dualUnitsDiagram_root R a i 1 (by decide) t

theorem dualAmbientDiagram_mem {g : WeightCompanionAmbient pairing base dualOrbits R}
    (hg : g ∈ weightCompanionSubgroup pairing base dualOrbits
      dualOrbits_closed dualOrbits_minuscule R) :
    dualAmbientDiagram R g ∈ weightCompanionSubgroup pairing base dualOrbits
      dualOrbits_closed dualOrbits_minuscule R := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨i, t, rfl⟩ | ⟨i, t, rfl⟩
    · rw [dualAmbientDiagram_X]
      exact Subgroup.subset_closure (Or.inl ⟨baseDiagram i, t, rfl⟩)
    · rw [dualAmbientDiagram_Y]
      exact Subgroup.subset_closure (Or.inr ⟨baseDiagram i, t, rfl⟩)
  | one => simpa only [map_one] using (weightCompanionSubgroup pairing base dualOrbits
      dualOrbits_closed dualOrbits_minuscule R).one_mem
  | mul g h hg hh ihg ihh => simpa only [map_mul] using Subgroup.mul_mem _ ihg ihh
  | inv g hg ih => simpa only [map_inv] using Subgroup.inv_mem _ ih

def dualCompanionDiagram : DualCompanion R ≃* DualCompanion R where
  toFun g := ⟨dualAmbientDiagram R g.val, dualAmbientDiagram_mem R g.property⟩
  invFun g := ⟨dualAmbientDiagram R g.val, dualAmbientDiagram_mem R g.property⟩
  left_inv g := Subtype.ext (dualAmbientDiagram_involutive R g.val)
  right_inv g := Subtype.ext (dualAmbientDiagram_involutive R g.val)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

theorem dualCompanionDiagram_involutive : Function.Involutive (dualCompanionDiagram R) := by
  intro g
  exact Subtype.ext (dualAmbientDiagram_involutive R g.val)

@[simp] theorem dualCompanionDiagram_X (i : base.support) (t : R) :
    dualCompanionDiagram R
      (weightCompanionX pairing base dualOrbits dualOrbits_closed dualOrbits_minuscule R i t) =
    weightCompanionX pairing base dualOrbits dualOrbits_closed dualOrbits_minuscule
      R (baseDiagram i) t := Subtype.ext (dualAmbientDiagram_X R i t)

@[simp] theorem dualCompanionDiagram_Y (i : base.support) (t : R) :
    dualCompanionDiagram R
      (weightCompanionY pairing base dualOrbits dualOrbits_closed dualOrbits_minuscule R i t) =
    weightCompanionY pairing base dualOrbits dualOrbits_closed dualOrbits_minuscule
      R (baseDiagram i) t := Subtype.ext (dualAmbientDiagram_Y R i t)

theorem dualCompanionDiagram_rho (g : DualCompanion R) :
    weightCompanionRho pairing base dualOrbits dualOrbits_closed dualOrbits_minuscule
      R (dualCompanionDiagram R g) =
    adjointDiagram R
      (weightCompanionRho pairing base dualOrbits dualOrbits_closed dualOrbits_minuscule R g) := rfl

end Atlas.Chevalley.TwistedE6

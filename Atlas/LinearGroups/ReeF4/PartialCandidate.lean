import Atlas.LinearGroups.ReeF4.StarLocalCompatibility

/-! Partial-product laws for the proposed extension, on the prescribed domain.
The full generator-preservation and stabilizer-identification gates remain open. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def proposedPartialProduct (σ : F →+* F) (u v : TraceZero F) (h : StarDomain u v) :
    TraceZero F := proposedStarSemilinear σ (domainWedge u v h)

theorem proposedPartialProduct_comm (σ : F →+* F) (u v : TraceZero F)
    (h : StarDomain u v) :
    proposedPartialProduct σ u v h =
      proposedPartialProduct σ v u ((starDomain_comm u v).mp h) := by
  unfold proposedPartialProduct
  congr 1
  apply Subtype.ext
  exact wedge_comm_charTwo u v

theorem proposedPartialProduct_add_left (σ : F →+* F) (u v w : TraceZero F)
    (hu : StarDomain u w) (hv : StarDomain v w) :
    proposedPartialProduct σ (u+v) w (starDomain_add_left hu hv) =
      proposedPartialProduct σ u w hu + proposedPartialProduct σ v w hv := by
  have hd : domainWedge (u+v) w (starDomain_add_left hu hv) =
      domainWedge u w hu + domainWedge v w hv := by
    apply Subtype.ext
    exact wedge_add_left u v w
  simp only [proposedPartialProduct, hd, _root_.map_add]

theorem wedge_smul_left (a : F) (u v : TraceZero F) :
    wedge (a • u) v = a • wedge u v :=
  (exteriorPower.ιMulti F 2).map_vecCons_smul ![v] a u

theorem wedge_smul_right (a : F) (u v : TraceZero F) :
    wedge u (a • v) = a • wedge u v := by
  rw [wedge_comm_charTwo, wedge_smul_left, wedge_comm_charTwo v u]

theorem proposedPartialProduct_smul (σ : F →+* F) (a b : F)
    (u v : TraceZero F) (h : StarDomain u v) :
    proposedPartialProduct σ (a • u) (b • v)
      (starDomain_smul_right b (starDomain_smul_left a h)) =
        σ (a*b) • proposedPartialProduct σ u v h := by
  have hd : domainWedge (a • u) (b • v)
      (starDomain_smul_right b (starDomain_smul_left a h)) =
        (a*b) • domainWedge u v h := by
    apply Subtype.ext
    simp only [domainWedge, Submodule.coe_smul, wedge_smul_left, wedge_smul_right, mul_smul]
    exact smul_comm b a (wedge u v)
  simp only [proposedPartialProduct, hd, LinearMap.map_smulₛₗ]

theorem proposedPartialProduct_perpendicular (σ : F →+* F) (r s : ShortRootLabel)
    (h : rootDot (scaledShortRoot r) (scaledShortRoot s) = 0) :
    proposedPartialProduct σ (rootVector r) (rootVector s) (rootDomain_perpendicular r s h) =
      rootVector (starRootTarget r s) := by
  change traceZeroMap σ (proposedStarLinear (wedge (rootVector r) (rootVector s))) = _
  rw [proposedStarLinear_perpendicular r s h]
  exact rootVector_map σ _

end Atlas.ReeF4

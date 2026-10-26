import Atlas.LinearGroups.ReeF4.SpecialIsotropy
import Atlas.LinearGroups.ReeF4.RootProductTables

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def leadingWitnessExamplePoint : TraceZero F := rootVector (2,7)
def leadingWitnessExampleLow : TraceZero F := rootVector (2,5)
def leadingWitnessExampleHigh : TraceZero F := rootVector (0,7)
def leadingWitnessExample : TraceZero F :=
  leadingWitnessExampleLow + leadingWitnessExampleHigh

theorem leadingWitnessExample_low_domain :
    StarDomain (leadingWitnessExamplePoint (F := F)) leadingWitnessExampleLow :=
  rootDomain_perpendicular (2,7) (2,5) (by decide)

theorem leadingWitnessExample_high_domain :
    StarDomain (leadingWitnessExamplePoint (F := F)) leadingWitnessExampleHigh := by
  constructor
  · rw [leadingWitnessExamplePoint,leadingWitnessExampleHigh,rootPolar]
    norm_num [Fin.ext_iff]
  · exact rootCross_noSum (2,7) (0,7) (by decide) (by decide)

theorem leadingWitnessExample_domain :
    StarDomain (leadingWitnessExamplePoint (F := F)) leadingWitnessExample := by
  apply (starDomain_comm _ _).mpr
  exact starDomain_add_left
    ((starDomain_comm _ _).mp leadingWitnessExample_low_domain)
    ((starDomain_comm _ _).mp leadingWitnessExample_high_domain)

theorem leadingWitnessExample_low_product (σ : F →+* F) :
    proposedPartialProduct σ leadingWitnessExamplePoint leadingWitnessExampleLow
      leadingWitnessExample_low_domain = leadingWitnessExamplePoint := by
  change proposedPartialProduct σ (rootVector (2,7)) (rootVector (2,5))
    (rootDomain_perpendicular (2,7) (2,5) (by decide)) = rootVector (2,7)
  rw [proposedPartialProduct_perpendicular σ (2,7) (2,5) (by decide)]
  have ht : starRootTarget (2,7) (2,5) = (2,7) := by decide
  rw [ht]

theorem leadingWitnessExample_high_raw_zero :
    proposedStarLinear (wedge (leadingWitnessExamplePoint (F := F))
      leadingWitnessExampleHigh) = 0 := by
  rw [leadingWitnessExamplePoint,leadingWitnessExampleHigh,
    ←markedBasis_root (2,7),←markedBasis_root (0,7),proposedStarLinear_marked_wedge]
  simp [extensionCoefficient,rootDot,scaledShortRoot]

theorem leadingWitnessExample_product (σ : F →+* F) :
    proposedPartialProduct σ leadingWitnessExamplePoint leadingWitnessExample
      leadingWitnessExample_domain = leadingWitnessExamplePoint := by
  change traceZeroMap σ (proposedStarLinear
    (wedge leadingWitnessExamplePoint (leadingWitnessExampleLow+leadingWitnessExampleHigh))) = _
  rw [wedge_add_right,_root_.map_add,leadingWitnessExample_high_raw_zero,add_zero]
  exact leadingWitnessExample_low_product σ

theorem leadingWitnessExample_point_isotropic :
    traceZeroQuadratic (leadingWitnessExamplePoint (F := F)) = 0 := by
  simp [leadingWitnessExamplePoint,rootVector,traceZeroQuadratic,quadraticTrace,
    SplitOctonion.norm,Pi.single_apply]

theorem leadingWitnessExample_witness_isotropic :
    traceZeroQuadratic (leadingWitnessExample (F := F)) = 0 := by
  simp [leadingWitnessExample,leadingWitnessExampleLow,leadingWitnessExampleHigh,
    rootVector,traceZeroQuadratic,quadraticTrace,SplitOctonion.norm,Pi.single_apply]

/-- The added component is the unique highest absolute-grade coordinate A4. -/
theorem leadingWitnessExample_top : (leadingWitnessExample (F := F)).val.2 0 7 = 1 := by
  simp [leadingWitnessExample,leadingWitnessExampleLow,leadingWitnessExampleHigh,
    rootVector,Pi.single_apply]
end Atlas.ReeF4

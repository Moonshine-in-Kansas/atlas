import Atlas.LinearGroups.ReeF4.SpecialMarkedLine
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Pairwise zero products on the concrete marked line. No global incidence
axioms, point count or transitivity are assumed. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem specialMarkedLine_basis_domain :
    StarDomain (rootVector (F := F) (0,0)) (rootVector (2,0)) := by
  constructor
  · rw [rootPolar]
    norm_num
  · exact rootCross_noSum (0,0) (2,0) (by decide) (by decide)

theorem specialMarkedLine_basis_rawStar_zero :
    proposedStarLinear (wedge (rootVector (F := F) (0,0)) (rootVector (2,0))) = 0 := by
  rw [← markedBasis_root (0,0), ← markedBasis_root (2,0),
    proposedStarLinear_marked_wedge]
  simp [extensionCoefficient, scaledShortRoot, rootDot]

private theorem markedLine_domain_add_right {u v w : TraceZero F}
    (huv : StarDomain u v) (huw : StarDomain u w) : StarDomain u (v+w) :=
  (starDomain_comm _ _).mpr (starDomain_add_left
    ((starDomain_comm _ _).mp huv) ((starDomain_comm _ _).mp huw))

theorem specialMarkedLine_combination_domain (a b c d : F) :
    StarDomain (a • rootVector (F := F) (0,0) + b • rootVector (2,0))
      (c • rootVector (F := F) (0,0) + d • rootVector (2,0)) := by
  have hef := specialMarkedLine_basis_domain (F := F)
  have hfe := (starDomain_comm _ _).mp hef
  exact starDomain_add_left
    (markedLine_domain_add_right
      (starDomain_smul_right c (starDomain_smul_left a (starDomain_self _)))
      (starDomain_smul_right d (starDomain_smul_left a hef)))
    (markedLine_domain_add_right
      (starDomain_smul_right c (starDomain_smul_left b hfe))
      (starDomain_smul_right d (starDomain_smul_left b (starDomain_self _))))

theorem specialMarkedLine_domain {u v : TraceZero F}
    (hu : u ∈ specialMarkedLine (F := F)) (hv : v ∈ specialMarkedLine (F := F)) :
    StarDomain u v := by
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hu
  obtain ⟨c,d,rfl⟩ := Submodule.mem_span_pair.mp hv
  exact specialMarkedLine_combination_domain a b c d

private theorem markedLine_wedge_self (u : TraceZero F) : wedge u u = 0 :=
  (exteriorPower.ιMulti F 2).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)

theorem specialMarkedLine_combination_rawStar_zero (a b c d : F) :
    proposedStarLinear (wedge (a • rootVector (F := F) (0,0) + b • rootVector (2,0))
      (c • rootVector (F := F) (0,0) + d • rootVector (2,0))) = 0 := by
  have hfe : proposedStarLinear (wedge (rootVector (F := F) (2,0))
      (rootVector (F := F) (0,0))) = 0 := by
    rw [wedge_comm_charTwo, specialMarkedLine_basis_rawStar_zero]
  simp only [wedge_add_left, wedge_add_right, wedge_smul_left, wedge_smul_right,
    markedLine_wedge_self, _root_.map_add, LinearMap.map_smul, _root_.map_zero,
    specialMarkedLine_basis_rawStar_zero, hfe, smul_zero, add_zero]

theorem specialMarkedLine_rawStar_zero {u v : TraceZero F}
    (hu : u ∈ specialMarkedLine (F := F)) (hv : v ∈ specialMarkedLine (F := F)) :
    proposedStarLinear (wedge u v) = 0 := by
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hu
  obtain ⟨c,d,rfl⟩ := Submodule.mem_span_pair.mp hv
  exact specialMarkedLine_combination_rawStar_zero a b c d

/-- Every pair in the marked span is admissible and has zero partial product,
even when one vector is zero or the two vectors are dependent. -/
theorem specialMarkedLine_partialProduct_zero (σ : F →+* F) {u v : TraceZero F}
    (hu : u ∈ specialMarkedLine (F := F)) (hv : v ∈ specialMarkedLine (F := F))
    (h : StarDomain u v) : proposedPartialProduct σ u v h = 0 := by
  change traceZeroMap σ (proposedStarLinear (wedge u v)) = 0
  rw [specialMarkedLine_rawStar_zero hu hv, traceZeroMap_zero]

/-- The marked span really is two-dimensional, by independence of its two
members of the already verified 26-element marked basis. -/
theorem finrank_specialMarkedLine : Module.finrank F (specialMarkedLine (F := F)) = 2 := by
  let f : Fin 2 → TraceZeroCoordinate := ![.inr (0,0),.inr (2,0)]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at *
  have hi := (markedBasis (F := F)).linearIndependent.comp f hf
  have hc := finrank_span_eq_card hi
  have hr : Set.range (fun i => markedBasis (f i)) =
      {rootVector (F := F) (0,0), rootVector (2,0)} := by
    ext v
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp [f,markedBasis_root]
    · rintro (rfl | rfl)
      · exact ⟨0,markedBasis_root _⟩
      · exact ⟨1,markedBasis_root _⟩
  change Module.finrank F (Submodule.span F (Set.range (fun i => markedBasis (f i)))) = 2 at hc
  rw [hr] at hc
  exact hc

end Atlas.ReeF4

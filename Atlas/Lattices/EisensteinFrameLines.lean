import Atlas.Lattices.EisensteinFrameVectors
import Atlas.Lattices.EisensteinShortLines

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The actual one-dimensional K-subspace through a norm-six lattice vector. -/
def eisensteinScalarLine (x : EisensteinShell 6) :
    Submodule EisensteinRational EisensteinRationalCoordinates :=
  Submodule.span EisensteinRational {eisensteinCoordinateEmbedding x.val.val}

theorem eisensteinScalarLine_eq_iff (x y : EisensteinShell 6) :
    eisensteinScalarLine y = eisensteinScalarLine x ↔
      ∃ c : EisensteinRational,
        eisensteinCoordinateEmbedding y.val.val = c • eisensteinCoordinateEmbedding x.val.val := by
  constructor
  · intro h
    have hy : eisensteinCoordinateEmbedding y.val.val ∈ eisensteinScalarLine x := by
      rw [← h]; exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    have hy := eisensteinEmbedding_ne_zero_of_norm y.val (by rw [y.property]; norm_num)
    have hn : c ≠ 0 := by intro h; rw [h, zero_smul] at hc; exact hy hc
    unfold eisensteinScalarLine
    rw [hc]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hn) _

theorem eisensteinScalarLine_finrank (x : EisensteinShell 6) :
    Module.finrank EisensteinRational (eisensteinScalarLine x) = 1 :=
  finrank_span_singleton (eisensteinEmbedding_ne_zero_of_norm x.val (by rw [x.property]; norm_num))

/-- Multiplication by any integral unit preserves a class up to sign. -/
theorem eisenstein_unit_class (u : Eisensteinˣ) (x : EisensteinLattice) :
    eisensteinClass ((u : Eisenstein) • x) = eisensteinClass x ∨
      eisensteinClass ((u : Eisenstein) • x) = -eisensteinClass x := by
  have hcc : eisensteinClass x + eisensteinClass x = -eisensteinClass x := by
    have h := eisensteinClasses_three (eisensteinClass x)
    have ht : eisensteinClass x + eisensteinClass x + eisensteinClass x = 0 := by
      simpa only [succ_nsmul, zero_nsmul, zero_add, add_zero, add_assoc] using h
    calc
      _ = (eisensteinClass x + eisensteinClass x + eisensteinClass x) - eisensteinClass x := by abel
      _ = _ := by rw [ht]; simp
  have hu := (eisenstein_norm_one_iff (u : Eisenstein)).mp ((eisenstein_isUnit_iff _).mp u.isUnit)
  rcases hu with hu | hu | hu | hu | hu | hu
  · left; rw [hu, one_smul]
  · right; rw [hu, neg_smul, one_smul, map_neg]
  · left; rw [hu]; exact eisensteinLatticeRotation_class x
  · right; rw [hu, neg_smul, map_neg]; exact congrArg Neg.neg (eisensteinLatticeRotation_class x)
  · right
    rw [hu, add_smul, map_add, one_smul]
    change eisensteinClass x + eisensteinClass (eisensteinLatticeRotation x) = _
    rw [eisensteinLatticeRotation_class, hcc]
  · left
    have he : (-1 - eisensteinOmega : Eisenstein) = -(1+eisensteinOmega) := by ring
    rw [hu, he, neg_smul, map_neg, add_smul, map_add, one_smul]
    change -(eisensteinClass x + eisensteinClass (eisensteinLatticeRotation x)) = _
    rw [eisensteinLatticeRotation_class, hcc, neg_neg]

/-- Frame vectors contain all six norm-six unit multiples of each of their vectors. -/
theorem eisensteinFrameVectors_unit_closed
    (F : EisensteinFrame) (x y : EisensteinShell 6)
    (hx : x ∈ eisensteinFrameVectors F) (u : Eisensteinˣ)
    (hy : y.val = (u : Eisenstein) • x.val) : y ∈ eisensteinFrameVectors F := by
  have hxclass := (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [hy]
  rcases eisenstein_unit_class u x.val with h | h
  · rw [h]; exact hxclass
  · rw [h]
    obtain ⟨c, hc, he⟩ := eisensteinFrame_pair F
    rw [he] at hxclass ⊢
    simpa [eisensteinFramePair, neg_eq_iff_eq_neg, or_comm] using hxclass

/-- Membership in the frame is constant along each norm-six scalar line. -/
theorem eisensteinFrameVectors_sameLine
    (F : EisensteinFrame) (x y : EisensteinShell 6)
    (hx : x ∈ eisensteinFrameVectors F)
    (hline : eisensteinScalarLine y = eisensteinScalarLine x) : y ∈ eisensteinFrameVectors F := by
  obtain ⟨u, hu⟩ := eisenstein_six_sameLine_unit x.val y.val x.property y.property
    ((eisensteinScalarLine_eq_iff x y).mp hline)
  exact eisensteinFrameVectors_unit_closed F x y hx u hu

/-- The intrinsic frame as a finite set of actual scalar lines. -/
def eisensteinFrameLines (F : EisensteinFrame) :
    Finset (Submodule EisensteinRational EisensteinRationalCoordinates) :=
  (eisensteinFrameVectors F).image eisensteinScalarLine

/-- Every line of a frame contains exactly six of its short vectors. -/
theorem eisensteinFrameLines_fiber (F : EisensteinFrame) (x : EisensteinShell 6)
    (hx : x ∈ eisensteinFrameVectors F) :
    ((eisensteinFrameVectors F).filter (fun y => eisensteinScalarLine y = eisensteinScalarLine x)).card = 6 := by
  have he : (eisensteinFrameVectors F).filter (fun y => eisensteinScalarLine y = eisensteinScalarLine x) =
      Finset.univ.filter (fun y => eisensteinScalarLine y = eisensteinScalarLine x) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨eisensteinFrameVectors_sameLine F x y hx h, h⟩⟩
  rw [he, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have eqv : {y : EisensteinShell 6 // eisensteinScalarLine y = eisensteinScalarLine x} ≃
      EisensteinSixLineFiber x := Equiv.subtypeEquivRight (fun y => eisensteinScalarLine_eq_iff x y)
  rw [Nat.card_congr eqv]
  exact eisenstein_six_line_card x

/-- Every intrinsic frame consists of exactly twelve scalar lines. -/
theorem eisensteinFrameLines_card (F : EisensteinFrame) : (eisensteinFrameLines F).card = 12 := by
  have h := Finset.card_eq_sum_card_image (s := eisensteinFrameVectors F) (f := eisensteinScalarLine)
  have hs : (∑ L ∈ (eisensteinFrameVectors F).image eisensteinScalarLine,
      ((eisensteinFrameVectors F).filter (fun x => eisensteinScalarLine x = L)).card) =
      (eisensteinFrameLines F).card * 6 := by
    calc
      _ = ∑ _L ∈ eisensteinFrameLines F, 6 := by
        apply Finset.sum_congr rfl
        intro L hL
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hL
        exact eisensteinFrameLines_fiber F x hx
      _ = _ := by simp
  rw [eisensteinFrameVectors_card, hs] at h
  omega

/-- The line set recovers exactly the short vectors of the intrinsic frame. -/
theorem eisensteinFrameLines_recovers_vectors (F : EisensteinFrame) (x : EisensteinShell 6) :
    eisensteinScalarLine x ∈ eisensteinFrameLines F ↔ x ∈ eisensteinFrameVectors F := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    exact eisensteinFrameVectors_sameLine F y x hy he.symm
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- Equality of the twelve-line configurations implies equality of the intrinsic frames. -/
theorem eisensteinFrameLines_injective : Function.Injective eisensteinFrameLines := by
  intro F G h
  apply eisensteinFrameVectors_injective
  ext x
  rw [← eisensteinFrameLines_recovers_vectors, ← eisensteinFrameLines_recovers_vectors, h]

end Atlas.Lattices

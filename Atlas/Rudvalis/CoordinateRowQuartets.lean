import Atlas.Rudvalis.CoordinateRowPairCount
import Atlas.Rudvalis.IntrinsicConfigurations
import Atlas.Rudvalis.HeavyOrthogonalLocal
import Atlas.Rudvalis.FourOrthogonalCount

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

/-- A noncoordinate minimum cannot vanish in exactly three of a row's four Gaussian pairs. -/
theorem minimumWord_row_zero_pairs_ne_six (w : MinimumWords) (p : Point) :
    Nat.card {x : E // reduce w.val.val (p,x)=0 ∧ reduce w.val.val (p,x+p.val)=0}≠6 := by
  classical
  rcases quaternary_minimum_support_cases w.val.val w.val.prop w.prop with hf|hh
  · have he (x : E) := fourSupport_pair_zero_iff _ hf p x
    rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
    by_cases h : ∀y : E,reduce w.val.val (p,y)=0
    · simp [Nat.card_eq_fintype_card,h,E,Bit,ZMod.card]
    · simp [h]
  · obtain ⟨a,hc,ha⟩ := hh
    have hw : hammingNorm (binaryNormalMap a)=16 := by
      rw [ha]
      exact quaternary_minimum_residue_weight _ w.val.prop w.prop
    have hb := (binaryNormalMap_quadratic_weight_sixteen a hc).mp hw p
    have hp := quadratic_row_zero_pairs (a.1 p) (matrixAt a.2.1 p.val+eta p a.2.2)
      a.2.2 p.val hc p.prop hb
    have he (x : E) : binaryNormalMap a (p,x)=a.1 p+dot (matrixAt a.2.1 p.val+eta p a.2.2) x+quadratic a.2.2 x := by
      change a.1 p+dot (matrixAt a.2.1 p.val) x+theta p a.2.2 x=_
      simp only [theta,dot_add_left]
      ring
    rw [←ha]
    simp_rw [he]
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    rw [hp]
    split <;> decide

theorem minimumWord_row_orthogonal_count_ne_three (w : MinimumWords) (p : Point) :
    Nat.card {c : coordinateRowFrame p // CrossOrthogonal (minimalCross (minimumWordShellLift w)) c.val}≠3 := by
  intro h3
  have hc := coordinateRow_predicate_card p (CrossOrthogonal (minimalCross (minimumWordShellLift w)))
  rw [h3] at hc
  have he (x : E) : CrossOrthogonal (minimalCross (minimumWordShellLift w)) (coordinateCross (p,x)) ↔
      reduce w.val.val (p,x)=0 ∧ reduce w.val.val (p,x+p.val)=0 := by
    rw [crossOrthogonal_symm,coordinateCross,crossOrthogonal_mk]
    change HermitianOrthogonal (coordinateMinimum (p,x)) (minimumWordShellLift w).val.val ↔ _
    rw [coordinate_hermitianOrthogonal_pair,minimumWordShellLift_zero_iff,minimumWordShellLift_zero_iff]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)] at hc
  exact minimumWord_row_zero_pairs_ne_six w p hc

/-- Every original coordinate row is an intrinsic quartet, with external-point exclusion. -/
theorem coordinateRowFrame_isQuartet (p : Point) : IsQuartet (coordinateRowFrame p) := by
  classical
  refine ⟨?_,?_,?_⟩
  · exact coordinateRowFrame_card p
  · intro x hx y hy hxy
    exact (coordinateFrame_orthogonal_iff _ _ (coordinateRowFrame_subset p hx)
      (coordinateRowFrame_subset p hy)).mpr hxy
  · intro x hx q hq hall
    induction x using Quotient.inductionOn with | h v =>
      rcases rudvalisLattice_shell_cases v.val.val v.val.prop v.prop with hv|⟨w,hw⟩
      · have hvf : minimalCross v∈coordinateFrame :=
          (minimalCross_mem_coordinateFrame v).mpr ((coordinateShellPiece_iff v).mpr hv)
        exact (coordinateFrame_orthogonal_iff _ _ hvf (coordinateRowFrame_subset p hq)).mpr
          (by intro he; apply hx; change minimalCross v∈coordinateRowFrame p; rwa [he])
      · have he : v=minimumWordShellLift w := Subtype.ext (Subtype.ext hw)
        subst v
        by_contra hnq
        have heq (y : coordinateRowFrame p) :
            CrossOrthogonal (minimalCross (minimumWordShellLift w)) y.val ↔ ¬y.val=q := by
          constructor
          · intro hy hyq
            exact hnq (hyq ▸ hy)
          · intro hy
            exact hall y.val y.prop hy
        let e : {y : coordinateRowFrame p // CrossOrthogonal (minimalCross (minimumWordShellLift w)) y.val} ≃
            {y : coordinateRowFrame p // ¬y=⟨q,hq⟩} :=
          Equiv.subtypeEquivRight (fun y => (heq y).trans (not_congr (show y.val=q ↔ y=⟨q,hq⟩ from ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩)))
        apply minimumWord_row_orthogonal_count_ne_three w p
        let : Fintype (coordinateRowFrame p) := Fintype.ofFinite _
        rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
        have h4 : Fintype.card (coordinateRowFrame p)=4 := by
          simpa [Nat.card_eq_fintype_card] using coordinateRowFrame_card p
        simp [h4]

end Atlas.Rudvalis

import Atlas.Rudvalis.HeavyLabelFusion
import Atlas.Rudvalis.HeavyOrthogonalCount

/-! The actual coordinate-cross stabilizer is transitive on its 1536 heavy neighbours. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem heavyAvoidingPair_label_ne (c p : Point) (v : HeavyAvoidingPair c p 0) : p≠c := by
  classical
  intro h
  subst p
  have hc := fixedHeavy_row_pairs_card c c v.val
  simp only [ite_true] at hc
  have hm : (0 : E)∈Finset.univ.filter (fun x : E =>
      fixedHeavyWord c v.val (c,x)=0 ∧ fixedHeavyWord c v.val (c,x+c.val)=0) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,v.prop⟩
  have hp := Finset.card_pos.mpr ⟨(0 : E),hm⟩
  omega

theorem heavyWord_avoiding_parameters (p : Point) (w : HeavyMinimumWords)
    (hw : reduce w.val.val (p,0)=0 ∧ reduce w.val.val (p,0+p.val)=0) :
    ∃c : Point,∃v : HeavyAvoidingPair c p 0,p≠c ∧ reduce w.val.val=fixedHeavyWord c v.val := by
  obtain ⟨a,hc,ha⟩ := w.prop.2
  have hweight : hammingNorm (binaryNormalMap a)=16 := by
    rw [ha]
    exact quaternary_minimum_residue_weight w.val.val w.val.prop w.prop.1
  let c : Point := ⟨a.2.2,hc⟩
  let v' : FixedHeavyParameters c :=
    ⟨⟨a.2.1,binaryNormalMap_quadratic_minimum_contraction a hc hweight⟩,⟨a.1,hweight⟩⟩
  have he : fixedHeavyWord c v'=reduce w.val.val := ha
  let v : HeavyAvoidingPair c p 0 := ⟨v',by rw [he];exact hw⟩
  exact ⟨c,v,heavyAvoidingPair_label_ne c p v,he.symm⟩

theorem heavyWord_coordinate_stabilizer_transitive (p : Point) (v w : HeavyMinimumWords)
    (hv : CrossOrthogonal (coordinateCross (p,0)) (minimalCross (minimumWordShellLift (heavyMinimumWord v))))
    (hw : CrossOrthogonal (coordinateCross (p,0)) (minimalCross (minimumWordShellLift (heavyMinimumWord w)))) :
    ∃g : codeGroup,g • coordinateCross (p,0)=coordinateCross (p,0) ∧
      monomialHom g.val v.val.val=w.val.val := by
  obtain ⟨c,a,hpc,ha⟩ := heavyWord_avoiding_parameters p v ((heavyWord_coordinate_orthogonal_iff v p 0).mp hv)
  obtain ⟨d,b,hpd,hb⟩ := heavyWord_avoiding_parameters p w ((heavyWord_coordinate_orthogonal_iff w p 0).mp hw)
  let v' : SignedLift quaternaryCode (fixedHeavyWord c a.val) :=
    ⟨v.val,ha,quaternary_minimum_no_twos _ v.val.prop v.prop.1⟩
  let w' : SignedLift quaternaryCode (fixedHeavyWord d b.val) :=
    ⟨w.val,hb,quaternary_minimum_no_twos _ w.val.prop w.prop.1⟩
  exact heavy_pair_all_labels_signedLift_transitive c d p hpc hpd a b v' w'

theorem heavyCross_rep (c : HeavyCrosses) :
    ∃w : HeavyMinimumWords,shellPieceCrossMap heavyShellPiece c=
      minimalCross (minimumWordShellLift (heavyMinimumWord w)) := by
  induction c using Quotient.inductionOn with
  | h v =>
    obtain ⟨w,hw⟩ := v.prop
    exact ⟨w,congrArg minimalCross hw.symm⟩

/-- Transitivity concerns the actual heavy Gaussian crosses, not a permutation replacement. -/
theorem heavyCross_coordinate_stabilizer_transitive (p : Point) (a b : HeavyCrosses)
    (ha : CrossOrthogonal (coordinateCross (p,0)) (shellPieceCrossMap heavyShellPiece a))
    (hb : CrossOrthogonal (coordinateCross (p,0)) (shellPieceCrossMap heavyShellPiece b)) :
    ∃g : codeGroup,g • coordinateCross (p,0)=coordinateCross (p,0) ∧
      g • shellPieceCrossMap heavyShellPiece a=shellPieceCrossMap heavyShellPiece b := by
  obtain ⟨v,hv⟩ := heavyCross_rep a
  obtain ⟨w,hw⟩ := heavyCross_rep b
  obtain ⟨g,hg,hvw⟩ := heavyWord_coordinate_stabilizer_transitive p v w (hv ▸ ha) (hw ▸ hb)
  refine ⟨g,hg,?_⟩
  have he : g • heavyMinimumWord v=heavyMinimumWord w := Subtype.ext (Subtype.ext hvw)
  rw [hv,hw,←minimalCross_smul,←minimumWordShellLift_equivariant,he]

end Atlas.Rudvalis

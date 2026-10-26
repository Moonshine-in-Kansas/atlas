import Atlas.Rudvalis.FourCrossLabels
import Atlas.Rudvalis.FourLocalOrbitSet

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

 theorem four_rowKernel_fixed_label_words (a : Point) (v w : FourMinimumWords)
    (hv : fourSupportNormal ⟨reduce v.val.val,v.prop.2⟩=a)
    (hw : fourSupportNormal ⟨reduce w.val.val,w.prop.2⟩=a) :
    ∃g : codeRowKernel,monomialHom g.val.val v.val.val=w.val.val := by
  let vp := fourSupportEquiv.symm ⟨reduce v.val.val,v.prop.2⟩
  let wp := fourSupportEquiv.symm ⟨reduce w.val.val,w.prop.2⟩
  have hva : vp.1=a := hv
  have hwa : wp.1=a := hw
  have hε : ∀p,dot a.val p.val=0 → vp.2.val.val p=0 := by rw [←hva]; exact vp.2.val.prop
  have hδ : ∀p,dot a.val p.val=0 → wp.2.val.val p=0 := by rw [←hwa]; exact wp.2.val.prop
  have hvn : binaryNormalMap (vp.2.val.val,outerMatrix a.val a.val,0)=reduce v.val.val := by
    have h := congrArg Subtype.val (fourSupportEquiv.apply_symm_apply ⟨reduce v.val.val,v.prop.2⟩)
    change binaryNormalMap (vp.2.val.val,outerMatrix vp.1.val vp.1.val,0)=_ at h
    rw [←hva]
    exact h
  have hwn : binaryNormalMap (wp.2.val.val,outerMatrix a.val a.val,0)=reduce w.val.val := by
    have h := congrArg Subtype.val (fourSupportEquiv.apply_symm_apply ⟨reduce w.val.val,w.prop.2⟩)
    change binaryNormalMap (wp.2.val.val,outerMatrix wp.1.val wp.1.val,0)=_ at h
    rw [←hwa]
    exact h
  obtain ⟨B,hB⟩ := four_support_fixed_form_translation a vp.2.val.val wp.2.val.val hε hδ
    (vp.2.prop.trans wp.2.prop.symm)
  obtain ⟨g,hg⟩ := codeRowKernel_translation_lift B
  let u := monomialHom g.val.val v.val.val
  have hur : reduce u=reduce w.val.val := by
    change reduce (monomialAction g.val.val v.val.val)=_
    rw [monomialAction_reduce,hg,←hvn,←hwn]
    exact hB.symm
  have hu : u∈quaternaryCode := (g.val.prop _).mp v.val.prop
  have hu16 : euclideanWeight u=16 := (monomial_euclideanWeight _ _).trans v.prop.1
  obtain ⟨h,hh⟩ := four_rowKernel_same_residue_transitive u w.val.val hu w.val.prop
    hu16 w.prop.1 (hur.symm ▸ w.prop.2) hur
  refine ⟨h*g,?_⟩
  change monomialHom (h.val.val*g.val.val) v.val.val=w.val.val
  rw [map_mul]
  exact hh

 theorem fourCrossHasLabel_rowKernel (g : codeRowKernel) (a : Point) (c : MinimalCross)
    (hc : FourCrossHasLabel a c) : FourCrossHasLabel a (g.val • c) := by
  obtain ⟨B,hB⟩ := codeRowKernel_coordinate_translation g⁻¹
  intro p x
  have h := crossOrthogonal_codeGroup g.val (g.val⁻¹ • coordinateCross (p,x)) c
  rw [smul_inv_smul] at h
  rw [h,coordinateCross_action]
  change CrossOrthogonal (coordinateCross ((g⁻¹).val.val.right (p,x))) c ↔ _
  rw [hB]
  exact hc p (x+matrixAt B p.val)

 theorem four_rowKernel_fixed_label_shell (a : Point) (v w : fourShellPiece)
    (hv : FourCrossHasLabel a (minimalCross v.val))
    (hw : FourCrossHasLabel a (minimalCross w.val)) :
    ∃g : codeRowKernel,g.val • v.val=w.val := by
  obtain ⟨v',hv'⟩ := v.prop
  obtain ⟨w',hw'⟩ := w.prop
  rw [←hv'] at hv
  rw [←hw'] at hw
  obtain ⟨g,hg⟩ := four_rowKernel_fixed_label_words a v' w'
    ((fourWord_label_iff a v').mp hv) ((fourWord_label_iff a w').mp hw)
  refine ⟨g,?_⟩
  rw [←hv',←hw',←minimumWordShellLift_equivariant]
  apply congrArg minimumWordShellLift
  exact Subtype.ext (Subtype.ext hg)

 theorem four_rowKernel_fixed_label_crosses (a : Point) (v w : FourBlockCrosses)
    (hv : FourCrossHasLabel a (shellPieceCrossMap fourShellPiece v))
    (hw : FourCrossHasLabel a (shellPieceCrossMap fourShellPiece w)) :
    ∃g : codeRowKernel,g.val • shellPieceCrossMap fourShellPiece v=shellPieceCrossMap fourShellPiece w := by
  induction v using Quotient.inductionOn with | h v =>
    induction w using Quotient.inductionOn with | h w =>
      obtain ⟨g,hg⟩ := four_rowKernel_fixed_label_shell a v w hv hw
      refine ⟨g,?_⟩
      change g.val • minimalCross v.val=minimalCross w.val
      rw [←minimalCross_smul,hg]

def fourLabelCrossPiece (a : Point) : Set MinimalCross :=
  {c | FourCrossHasLabel a c ∧ ∃v : FourBlockCrosses,shellPieceCrossMap fourShellPiece v=c}

noncomputable def fourLabelCrossPieceEquiv (a : Point) :
    {v : FourBlockCrosses // FourCrossHasLabel a (shellPieceCrossMap fourShellPiece v)} ≃ fourLabelCrossPiece a :=
  Equiv.ofBijective (fun v=>⟨shellPieceCrossMap fourShellPiece v.val,v.prop,v.val,rfl⟩) (by
    constructor
    · intro u v h; exact Subtype.ext (shellPieceCrossMap_injective _ (congrArg Subtype.val h))
    · rintro ⟨c,hc,v,rfl⟩; exact ⟨⟨v,hc⟩,rfl⟩)

 theorem fourLabelCrossPiece_card (a : Point) : Nat.card (fourLabelCrossPiece a)=64 := by
  rw [←Nat.card_congr (fourLabelCrossPieceEquiv a),fourLabelCrosses_card]

 theorem fourCross_rowKernel_orbit (a : Point) (v : FourBlockCrosses)
    (hv : FourCrossHasLabel a (shellPieceCrossMap fourShellPiece v)) :
    MulAction.orbit codeRowKernel (shellPieceCrossMap fourShellPiece v)=fourLabelCrossPiece a := by
  ext c
  constructor
  · intro hc
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hc
    exact ⟨fourCrossHasLabel_rowKernel g a _ hv,shellPieceCross_range_stable fourShellPiece g.val _ ⟨v,rfl⟩⟩
  · rintro ⟨hc,w,rfl⟩
    obtain ⟨g,hg⟩ := four_rowKernel_fixed_label_crosses a v w hv hc
    exact MulAction.mem_orbit_iff.mpr ⟨g,hg⟩

 theorem fourCross_label_exists (v : FourBlockCrosses) : ∃a : Point,FourCrossHasLabel a (shellPieceCrossMap fourShellPiece v) := by
  induction v using Quotient.inductionOn with
  | h v =>
    obtain ⟨w,hw⟩ := v.prop
    change ∃a,FourCrossHasLabel a (minimalCross v.val)
    rw [←hw]
    exact ⟨fourSupportNormal ⟨reduce w.val.val,w.prop.2⟩,(fourWord_label_iff _ w).mpr rfl⟩

 theorem fourCross_rowKernel_orbit_card (v : FourBlockCrosses) :
    Nat.card (MulAction.orbit codeRowKernel (shellPieceCrossMap fourShellPiece v))=64 := by
  obtain ⟨a,ha⟩ := fourCross_label_exists v
  rw [fourCross_rowKernel_orbit a v ha,fourLabelCrossPiece_card]

 theorem fourCross_rowKernel_stabilizer_order (v : FourBlockCrosses) :
    Nat.card (MulAction.stabilizer codeRowKernel (shellPieceCrossMap fourShellPiece v))=128 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup codeRowKernel (shellPieceCrossMap fourShellPiece v))
  rw [Nat.card_prod,fourCross_rowKernel_orbit_card,codeRowKernel_order] at h
  omega

end Atlas.Rudvalis

import Atlas.Rudvalis.FourRowKernelFibre
import Atlas.Rudvalis.HeavyFixedTranslation
import Atlas.Rudvalis.HeavySignTransitivity
import Atlas.Rudvalis.HeavyCrossLabels
import Atlas.Rudvalis.HeavyLocalOrbitSet

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem heavy_fixedLabel_rowKernel_transitive (c : Point)
    (v w : FixedHeavyParameters c)
    (a : SignedLift quaternaryCode (fixedHeavyWord c v))
    (b : SignedLift quaternaryCode (fixedHeavyWord c w)) :
    ∃g : codeRowKernel,monomialHom g.val.val a.val.val=b.val.val := by
  obtain ⟨A,hA⟩ := quadratic_minimum_fixed_radical_translation v.2.val w.2.val
    v.1.val w.1.val c.val c.prop v.2.prop w.2.prop
  obtain ⟨g,hgr⟩ := codeRowKernel_translation_lift A
  have hgs : g.val.val.right.symm=coordinateTranslation A := by rw [hgr]; rfl
  let a' : SignedLift quaternaryCode (fixedHeavyWord c w) :=
    ⟨⟨monomialHom g.val.val a.val.val,(g.val.prop _).mp a.val.prop⟩,by
      change reduce (monomialAction g.val.val a.val.val)=fixedHeavyWord c w
      rw [monomialAction_reduce,a.prop.1,hgs]
      exact hA.symm,monomial_no_twos g.val.val a.val.val a.prop.2⟩
  have hd : hasNonzeroQuadraticPart (fixedHeavyWord c w) :=
    ⟨(w.2.val,w.1.val,c.val),c.prop,rfl⟩
  obtain ⟨k,hkr,hk⟩ := heavy_signedLift_sign_transitive (fixedHeavyWord c w) hd w.2.prop a' b
  have hkP : k∈codeRowKernel := codeRowKernel_mem_of_rows k (by intro z; rw [hkr]; rfl)
  refine ⟨⟨k,hkP⟩*g,?_⟩
  change monomialHom (k.val*g.val.val) a.val.val=b.val.val
  rw [map_mul]
  exact hk

theorem heavy_rowKernel_fixed_label_words (p : Point) (v w : HeavyMinimumWords)
    (hv : heavyWordLabel v=p) (hw : heavyWordLabel w=p) :
    ∃g : codeRowKernel,monomialHom g.val.val v.val.val=w.val.val := by
  have hpa : ∃a : FixedHeavyParameters p,reduce v.val.val=fixedHeavyWord p a := by
    exact hv ▸ heavyWord_parameters v
  have hpb : ∃b : FixedHeavyParameters p,reduce w.val.val=fixedHeavyWord p b := by
    exact hw ▸ heavyWord_parameters w
  obtain ⟨a,ha⟩ := hpa
  obtain ⟨b,hb⟩ := hpb
  exact heavy_fixedLabel_rowKernel_transitive p a b
    ⟨v.val,ha,quaternary_minimum_no_twos _ v.val.prop v.prop.1⟩
    ⟨w.val,hb,quaternary_minimum_no_twos _ w.val.prop w.prop.1⟩

theorem heavyCrossHasLabel_rowKernel (g : codeRowKernel) (p : Point) (c : MinimalCross)
    (hc : HeavyCrossHasLabel p c) : HeavyCrossHasLabel p (g.val • c) := by
  obtain ⟨B,hB⟩ := codeRowKernel_coordinate_translation g⁻¹
  intro x
  have h := crossOrthogonal_codeGroup g.val (g.val⁻¹ • coordinateCross (p,x)) c
  rw [smul_inv_smul] at h
  rw [h,coordinateCross_action]
  change ¬CrossOrthogonal (coordinateCross ((g⁻¹).val.val.right (p,x))) c
  rw [hB]
  exact hc (x+matrixAt B p.val)

theorem heavy_rowKernel_fixed_label_shell (p : Point) (v w : heavyShellPiece)
    (hv : HeavyCrossHasLabel p (minimalCross v.val))
    (hw : HeavyCrossHasLabel p (minimalCross w.val)) :
    ∃g : codeRowKernel,g.val • v.val=w.val := by
  obtain ⟨v',hv'⟩ := v.prop
  obtain ⟨w',hw'⟩ := w.prop
  rw [←hv'] at hv
  rw [←hw'] at hw
  obtain ⟨g,hg⟩ := heavy_rowKernel_fixed_label_words p v' w'
    ((heavyWord_label_iff p v').mp hv) ((heavyWord_label_iff p w').mp hw)
  refine ⟨g,?_⟩
  rw [←hv',←hw',←minimumWordShellLift_equivariant]
  apply congrArg minimumWordShellLift
  exact Subtype.ext (Subtype.ext hg)

theorem heavy_rowKernel_fixed_label_crosses (p : Point) (v w : HeavyCrosses)
    (hv : HeavyCrossHasLabel p (shellPieceCrossMap heavyShellPiece v))
    (hw : HeavyCrossHasLabel p (shellPieceCrossMap heavyShellPiece w)) :
    ∃g : codeRowKernel,g.val • shellPieceCrossMap heavyShellPiece v=shellPieceCrossMap heavyShellPiece w := by
  induction v using Quotient.inductionOn with | h v =>
    induction w using Quotient.inductionOn with | h w =>
      obtain ⟨g,hg⟩ := heavy_rowKernel_fixed_label_shell p v w hv hw
      refine ⟨g,?_⟩
      change g.val • minimalCross v.val=minimalCross w.val
      rw [←minimalCross_smul,hg]

def heavyLabelCrossPiece (p : Point) : Set MinimalCross :=
  {c | HeavyCrossHasLabel p c ∧ ∃v : HeavyCrosses,shellPieceCrossMap heavyShellPiece v=c}

noncomputable def heavyLabelCrossPieceEquiv (p : Point) :
    {v : HeavyCrosses // HeavyCrossHasLabel p (shellPieceCrossMap heavyShellPiece v)} ≃ heavyLabelCrossPiece p :=
  Equiv.ofBijective (fun v=>⟨shellPieceCrossMap heavyShellPiece v.val,v.prop,v.val,rfl⟩) (by
    constructor
    · intro u v h; exact Subtype.ext (shellPieceCrossMap_injective _ (congrArg Subtype.val h))
    · rintro ⟨c,hc,v,rfl⟩; exact ⟨⟨v,hc⟩,rfl⟩)

theorem heavyLabelCrossPiece_card (p : Point) : Nat.card (heavyLabelCrossPiece p)=512 := by
  rw [←Nat.card_congr (heavyLabelCrossPieceEquiv p),heavyLabelCrosses_card]

theorem heavyCross_rowKernel_orbit (p : Point) (v : HeavyCrosses)
    (hv : HeavyCrossHasLabel p (shellPieceCrossMap heavyShellPiece v)) :
    MulAction.orbit codeRowKernel (shellPieceCrossMap heavyShellPiece v)=heavyLabelCrossPiece p := by
  ext c
  constructor
  · intro hc
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hc
    exact ⟨heavyCrossHasLabel_rowKernel g p _ hv,shellPieceCross_range_stable heavyShellPiece g.val _ ⟨v,rfl⟩⟩
  · rintro ⟨hc,w,rfl⟩
    obtain ⟨g,hg⟩ := heavy_rowKernel_fixed_label_crosses p v w hv hc
    exact MulAction.mem_orbit_iff.mpr ⟨g,hg⟩

theorem heavyCross_label_exists (v : HeavyCrosses) : ∃p : Point,HeavyCrossHasLabel p (shellPieceCrossMap heavyShellPiece v) := by
  induction v using Quotient.inductionOn with
  | h v =>
    obtain ⟨w,hw⟩ := v.prop
    change ∃p,HeavyCrossHasLabel p (minimalCross v.val)
    rw [←hw]
    exact ⟨heavyWordLabel w,(heavyWord_label_iff _ w).mpr rfl⟩

theorem heavyCross_rowKernel_orbit_card (v : HeavyCrosses) :
    Nat.card (MulAction.orbit codeRowKernel (shellPieceCrossMap heavyShellPiece v))=512 := by
  obtain ⟨p,hp⟩ := heavyCross_label_exists v
  rw [heavyCross_rowKernel_orbit p v hp,heavyLabelCrossPiece_card]

theorem heavyCross_rowKernel_stabilizer_order (v : HeavyCrosses) :
    Nat.card (MulAction.stabilizer codeRowKernel (shellPieceCrossMap heavyShellPiece v))=16 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup codeRowKernel (shellPieceCrossMap heavyShellPiece v))
  rw [Nat.card_prod,heavyCross_rowKernel_orbit_card,codeRowKernel_order] at h
  omega

end Atlas.Rudvalis


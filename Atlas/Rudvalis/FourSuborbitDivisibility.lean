import Atlas.Rudvalis.FourActiveLabelAction
import Atlas.GroupTheory.InvariantOrbitDivisibility
import Atlas.GroupTheory.SuborbitDivisibility

namespace Atlas.Rudvalis
open scoped BigOperators

 theorem fourCross_rowReference_orbit_divisible (v : FourBlockCrosses) :
    16∣Nat.card (MulAction.orbit codeRowReferenceStabilizer (shellPieceCrossMap fourShellPiece v)) := by
  apply Atlas.suborbit_card_divisible codeRowReferenceStabilizer _ 16
  rw [codeRowReferenceStabilizer_order,fourCross_rowKernel_stabilizer_order]

 def rowReferenceToCodeReference : codeRowReferenceStabilizer →* codeReferenceStabilizer where
  toFun g := ⟨g.val.val,g.prop⟩
  map_one' := rfl
  map_mul' _ _ := rfl

 theorem four_reference_orbit_range (v : FourBlockCrosses) (d : MinimalCross)
    (hd : d∈MulAction.orbit codeReferenceStabilizer (shellPieceCrossMap fourShellPiece v)) :
    ∃w : FourBlockCrosses,shellPieceCrossMap fourShellPiece w=d := by
  obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hd
  exact shellPieceCross_range_stable fourShellPiece g.val _ ⟨v,rfl⟩

 theorem codeReference_orbit_nonorthogonal (c d : MinimalCross)
    (hn : ¬CrossOrthogonal localReferenceCross c)
    (hd : d∈MulAction.orbit codeReferenceStabilizer c) : ¬CrossOrthogonal localReferenceCross d := by
  obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hd
  have h := crossOrthogonal_codeGroup g.val localReferenceCross c
  rw [show g.val • localReferenceCross=localReferenceCross from g.prop] at h
  exact fun he=>hn (h.mp he)

abbrev ActiveFourLabels := {a : Point // dot a.val (rowLabel 0).val=1}

theorem activeFourLabels_card : Nat.card ActiveFourLabels=4 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

def fourReferenceOrbitLabelFibre (c : MinimalCross) (a : Point) : Set MinimalCross :=
  {d | d∈MulAction.orbit codeReferenceStabilizer c ∧ FourCrossHasLabel a d}

noncomputable def fourReferenceOrbitLabelEquiv (c : MinimalCross) (a b : ActiveFourLabels) :
    fourReferenceOrbitLabelFibre c a.val ≃ fourReferenceOrbitLabelFibre c b.val := by
  let h := codeReferenceStabilizer_active_forms a.val b.val a.prop b.prop
  let g := h.choose
  have hg : ∀v : E,dot b.val.val (codeBlockLinearHom g.val v)=dot a.val.val v := h.choose_spec
  have hinv (v : E) : dot a.val.val (codeBlockLinearHom g.val⁻¹ v)=dot b.val.val v := by
    have h := hg (codeBlockLinearHom g.val⁻¹ v)
    have he : codeBlockLinearHom g.val (codeBlockLinearHom g.val⁻¹ v)=v := by
      rw [map_inv]
      exact (codeBlockLinearHom g.val).apply_symm_apply v
    rw [he] at h
    exact h.symm
  exact
    { toFun := fun d=>⟨g.val • d.val,
        MulAction.mapsTo_smul_orbit g c d.prop.1,
        fourCrossHasLabel_transport g.val a.val b.val hg d.val d.prop.2⟩
      invFun := fun d=>⟨g.val⁻¹ • d.val,
        MulAction.mapsTo_smul_orbit g⁻¹ c d.prop.1,
        fourCrossHasLabel_transport g.val⁻¹ b.val a.val hinv d.val d.prop.2⟩
      left_inv := fun d=>Subtype.ext (inv_smul_smul g.val d.val)
      right_inv := fun d=>Subtype.ext (smul_inv_smul g.val d.val) }

 theorem fourReferenceOrbitLabelFibre_divisible (v : FourBlockCrosses) (a : Point) :
    16∣Nat.card (fourReferenceOrbitLabelFibre (shellPieceCrossMap fourShellPiece v) a) := by
  refine Atlas.GroupTheory.invariant_card_dvd_of_orbits
    (G:=codeRowReferenceStabilizer) _ (Set.toFinite _) ?_ 16 ?_
  · intro g d hd
    exact ⟨MulAction.mapsTo_smul_orbit (rowReferenceToCodeReference g) _ hd.1,
      fourCrossHasLabel_rowKernel g.val a d hd.2⟩
  · intro d hd
    obtain ⟨w,rfl⟩ := four_reference_orbit_range v d hd.1
    exact fourCross_rowReference_orbit_divisible w

 theorem four_reference_orbit_divisible (v : FourBlockCrosses)
    (hn : ¬CrossOrthogonal localReferenceCross (shellPieceCrossMap fourShellPiece v)) :
    64∣Nat.card (MulAction.orbit codeReferenceStabilizer (shellPieceCrossMap fourShellPiece v)) := by
  classical
  let c := shellPieceCrossMap fourShellPiece v
  let O := MulAction.orbit codeReferenceStabilizer c
  have hex (d : O) : ∃a : ActiveFourLabels,FourCrossHasLabel a.val d.val := by
    obtain ⟨w,hw⟩ := four_reference_orbit_range v d.val d.prop
    obtain ⟨a,ha⟩ := fourCross_label_exists w
    rw [hw] at ha
    exact ⟨⟨a,fourCrossHasLabel_active a d.val ha (codeReference_orbit_nonorthogonal c d.val hn d.prop)⟩,ha⟩
  let f : O→ActiveFourLabels := fun d=>(hex d).choose
  have hf (d : O) : FourCrossHasLabel (f d).val d.val := (hex d).choose_spec
  have hiff (d : O) (a : ActiveFourLabels) : f d=a ↔ FourCrossHasLabel a.val d.val := by
    constructor
    · intro h; simpa only [h] using hf d
    · intro h; exact Subtype.ext (fourCrossHasLabel_unique (hf d) h)
  let e (a : ActiveFourLabels) : {d : O // f d=a} ≃ fourReferenceOrbitLabelFibre c a.val :=
    { toFun := fun d=>⟨d.val.val,d.val.prop,(hiff d.val a).mp d.prop⟩
      invFun := fun d=>⟨⟨d.val,d.prop.1⟩,(hiff ⟨d.val,d.prop.1⟩ a).mpr d.prop.2⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  let a₀ := f ⟨c,MulAction.mem_orbit_self c⟩
  have heq (a : ActiveFourLabels) : Nat.card {d : O // f d=a}=
      Nat.card (fourReferenceOrbitLabelFibre c a₀.val) :=
    (Nat.card_congr (e a)).trans (Nat.card_congr (fourReferenceOrbitLabelEquiv c a a₀))
  have hc : Nat.card O=4*Nat.card (fourReferenceOrbitLabelFibre c a₀.val) := by
    rw [←Nat.card_congr (Equiv.sigmaFiberEquiv f),Nat.card_sigma]
    simp_rw [heq]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
    rw [←Nat.card_eq_fintype_card,activeFourLabels_card]
  obtain ⟨k,hk⟩ := fourReferenceOrbitLabelFibre_divisible v a₀.val
  refine ⟨k,?_⟩
  change Nat.card O=64*k
  rw [hc,hk]
  omega

end Atlas.Rudvalis

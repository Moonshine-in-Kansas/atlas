import Atlas.Rudvalis.CrossRowEnergy
import Atlas.Rudvalis.HeavySelectedRowWeights
import Atlas.Rudvalis.FourCommonPerpendicular

namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary
open Classical
local instance : DecidablePred (fun p : Point => p∈referenceDozenRows) :=
  fun p => inferInstanceAs (Decidable (dot (binaryLabel 1) p.val=0))

/-- Number of active rows inside the selected coordinate dozen. -/
def fourSelectedRows (a : Point) : ℕ :=
  (Finset.univ.filter (fun p : Point => p∈referenceDozenRows ∧ dot a.val p.val≠0)).card

theorem fourSupport_parameter_row_weight (v : FourSupportParameters) (p : Point) :
    hammingNorm (fun x => (fourSupportEquiv v).val (p,x))=
      if dot v.1.val p.val=0 then 0 else 4 := by
  have he : (fun x => (fourSupportEquiv v).val (p,x))=
      (fun x => v.2.val.val p+dot (dot v.1.val p.val • v.1.val) x+quadratic 0 x) := by
    funext x
    change _+dot (matrixAt (outerMatrix v.1.val v.1.val) p.val) x+theta p 0 x=_
    simp [matrixAt_outer,theta_zero_parameter,quadratic]
  rw [he]
  change blockWeight _ _ 0=_
  rw [blockWeight_affine]
  by_cases h : dot v.1.val p.val=0
  · simp [h,v.2.val.prop p h]
  · simp [smul_eq_zero,h,v.1.prop]

theorem fourSupport_selected_weight (v : FourSupportParameters) :
    (∑p : Point,if p∈referenceDozenRows then
      hammingNorm (fun x => (fourSupportEquiv v).val (p,x)) else 0)=
      4*fourSelectedRows v.1 := by
  simp_rw [fourSupport_parameter_row_weight]
  unfold fourSelectedRows
  rw [Finset.card_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p∈referenceDozenRows <;>
    by_cases ha : dot v.1.val p.val=0 <;> simp [hp,ha]

theorem fourSelectedRows_reference (a : Point) (ha : dot a.val (rowLabel 0).val=0) :
    fourSelectedRows a=if a.val=binaryLabel 1 then 0 else 2 := by
  unfold fourSelectedRows referenceDozenRows
  simp only [Set.mem_ofPred_eq]
  revert ha
  decide +kernel +revert

theorem fourMinimumLift_energy (v : FourSupportParameters)
    (w : minimumLift (fourSupportEquiv v).val) :
    coordinateRowEnergy referenceDozenRows
      (halfCoordinates (integerLift w.val.val))=fourSelectedRows v.1 := by
  rw [coordinateRowEnergy_half]
  have hh := fourSupport_selected_weight v
  have hr := w.prop.2
  have he : (∑i : Coordinate,if i.1∈referenceDozenRows
      then (integerLift w.val.val i : ℚ)^2 else 0)=4*fourSelectedRows v.1 := by
    rw [Fintype.sum_prod_type]
    have hi(p : Point) : (∑x : E,if p∈referenceDozenRows
        then (integerLift w.val.val (p,x) : ℚ)^2 else 0)=
        if p∈referenceDozenRows then
          (hammingNorm (fun x => (fourSupportEquiv v).val (p,x)) : ℚ) else 0 := by
      by_cases hp : p∈referenceDozenRows
      · simp only [hp,ite_true]
        have h := minimumWord_integerLift_row_square ⟨w.val,w.prop.1⟩ p
        change (∑x : E,integerLift w.val.val (p,x)^2)=
          (hammingNorm (fun x => reduce w.val.val (p,x)) : ℤ) at h
        rw [hr] at h
        exact_mod_cast h
      · simp [hp]
    simp_rw [hi]
    exact_mod_cast hh
  calc
    _ = (4*(fourSelectedRows v.1 : ℚ))/4 := by
      congr 1
      convert he using 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.1∈referenceDozenRows <;> simp [hi]
    _ = _ := by ring



noncomputable def fourSupportNormal (d : {d : BinaryWord // admissibleFourSupport d}) : Point :=
  (fourSupportEquiv.symm d).1

abbrev FourEnergySupports (k : ℕ) :=
  {d : {d : BinaryWord // admissibleFourSupport d} //
    dot (fourSupportNormal d).val (rowLabel 0).val=0 ∧ fourSelectedRows (fourSupportNormal d)=k}

noncomputable def fourEnergySupportsEquiv (k : ℕ) : FourEnergySupports k ≃
    Σa : {a : Point // dot a.val (rowLabel 0).val=0 ∧ fourSelectedRows a=k},OddActiveConstants a.val :=
  (Equiv.subtypeEquiv fourSupportEquiv (fun v => by
    simp only [fourSupportNormal,Equiv.symm_apply_apply])).symm.trans
      (Equiv.subtypeSigmaEquiv OddActiveConstants _)

theorem fourSelectedRows_zero_labels :
    Nat.card {a : Point // dot a.val (rowLabel 0).val=0 ∧ fourSelectedRows a=0}=1 := by
  rw [Nat.card_eq_fintype_card]
  unfold fourSelectedRows referenceDozenRows
  decide +kernel

theorem fourSelectedRows_two_labels :
    Nat.card {a : Point // dot a.val (rowLabel 0).val=0 ∧ fourSelectedRows a=2}=2 := by
  rw [Nat.card_eq_fintype_card]
  unfold fourSelectedRows referenceDozenRows
  decide +kernel

theorem fourEnergySupports_card (k : ℕ) :
    Nat.card (FourEnergySupports k)=
      Nat.card {a : Point // dot a.val (rowLabel 0).val=0 ∧ fourSelectedRows a=k}*8 := by
  rw [Nat.card_congr (fourEnergySupportsEquiv k),Nat.card_sigma]
  simp_rw [oddActiveConstants_card]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]

abbrev FourEnergyWords (k : ℕ) :=
  {w : FourMinimumWords //
    dot (fourSupportNormal ⟨reduce w.val.val,w.prop.2⟩).val (rowLabel 0).val=0 ∧
    fourSelectedRows (fourSupportNormal ⟨reduce w.val.val,w.prop.2⟩)=k}

noncomputable def fourEnergyWordsEquiv (k : ℕ) :
    FourEnergyWords k ≃ Σd : FourEnergySupports k,minimumLift d.val.val :=
  (Equiv.subtypeEquiv fourMinimumWordsEquiv (fun _ => Iff.rfl)).trans
    (Equiv.subtypeSigmaEquiv (fun d : {d : BinaryWord // admissibleFourSupport d} => minimumLift d.val)
      (fun d => dot (fourSupportNormal d).val (rowLabel 0).val=0 ∧ fourSelectedRows (fourSupportNormal d)=k))

theorem fourEnergyWords_card (k : ℕ) :
    Nat.card (FourEnergyWords k)=Nat.card (FourEnergySupports k)*32 := by
  rw [Nat.card_congr (fourEnergyWordsEquiv k),Nat.card_sigma]
  simp_rw [four_minimum_fibre_card _ (Subtype.prop _)]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]

theorem fourWord_energy (w : FourMinimumWords) :
    coordinateRowEnergy referenceDozenRows (minimumWordShellLift (fourMinimumWord w)).val.val=
      fourSelectedRows (fourSupportNormal ⟨reduce w.val.val,w.prop.2⟩) := by
  let d : {d : BinaryWord // admissibleFourSupport d} := ⟨reduce w.val.val,w.prop.2⟩
  let v := fourSupportEquiv.symm d
  have hd : (fourSupportEquiv v).val=reduce w.val.val :=
    congrArg Subtype.val (fourSupportEquiv.apply_symm_apply d)
  exact fourMinimumLift_energy v ⟨w.val,w.prop.1,hd.symm⟩

theorem fourWord_reference_couple_normal (w : FourMinimumWords) :
    ReferenceCoupleOrthogonal (minimalCross (minimumWordShellLift (fourMinimumWord w))) ↔
      dot (fourSupportNormal ⟨reduce w.val.val,w.prop.2⟩).val (rowLabel 0).val=0 := by
  rw [ReferenceCoupleOrthogonal,localReferenceCross_eq,referenceSecondCross_eq,
    fourWord_coordinate_orthogonal_iff,fourWord_coordinate_orthogonal_iff,and_self]
  let d : {d : BinaryWord // admissibleFourSupport d} := ⟨reduce w.val.val,w.prop.2⟩
  have h := fourSupport_parameter_row_zero (fourSupportEquiv.symm d) (rowLabel 0)
  simpa only [Equiv.apply_symm_apply,d,fourSupportNormal] using h

noncomputable def fourEnergyShellEquiv (k : ℕ) :
    FourEnergyWords k ≃ RestrictedShellPiece fourShellPiece
      (fun c => ReferenceCoupleOrthogonal c ∧ crossRowEnergy referenceDozenRows c=k) :=
  Equiv.subtypeEquiv fourWordShellEquiv (fun w => by
    change (_ ∧ _=k) ↔ (ReferenceCoupleOrthogonal (minimalCross (minimumWordShellLift (fourMinimumWord w))) ∧
      crossRowEnergy referenceDozenRows (minimalCross (minimumWordShellLift (fourMinimumWord w)))=(k:ℚ))
    rw [fourWord_reference_couple_normal,crossRowEnergy_mk,fourWord_energy]
    exact and_congr_right (fun _ => Nat.cast_inj.symm))

theorem fourCouple_energy_zero_card :
    Nat.card {c : FourBlockCrosses // ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece c) ∧
      crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece c)=0}=64 := by
  have h := restricted_shell_cross_card fourShellPiece
    (fun c => ReferenceCoupleOrthogonal c ∧ crossRowEnergy referenceDozenRows c=(0:ℕ))
  rw [←Nat.card_congr (fourEnergyShellEquiv 0),fourEnergyWords_card,fourEnergySupports_card,
    fourSelectedRows_zero_labels] at h
  norm_num at h ⊢
  have hh : 256=Nat.card {c : FourBlockCrosses // ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece c) ∧
      crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece c)=0}*4 := h
  omega

theorem fourCouple_energy_two_card :
    Nat.card {c : FourBlockCrosses // ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece c) ∧
      crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece c)=2}=128 := by
  have h := restricted_shell_cross_card fourShellPiece
    (fun c => ReferenceCoupleOrthogonal c ∧ crossRowEnergy referenceDozenRows c=(2:ℕ))
  rw [←Nat.card_congr (fourEnergyShellEquiv 2),fourEnergyWords_card,fourEnergySupports_card,
    fourSelectedRows_two_labels] at h
  norm_num at h ⊢
  have hh : 512=Nat.card {c : FourBlockCrosses // ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece c) ∧
      crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece c)=2}*4 := h
  omega



theorem fourCouple_energy_cases (c : FourBlockCrosses)
    (hc : ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece c)) :
    crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece c)=0 ∨
      crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece c)=2 := by
  induction c using Quotient.inductionOn with
  | h v =>
    obtain ⟨w,rfl⟩ := fourWordShellEquiv.surjective v
    change ReferenceCoupleOrthogonal (minimalCross (minimumWordShellLift (fourMinimumWord w))) at hc
    change coordinateRowEnergy referenceDozenRows (minimumWordShellLift (fourMinimumWord w)).val.val=0 ∨
      coordinateRowEnergy referenceDozenRows (minimumWordShellLift (fourMinimumWord w)).val.val=2
    rw [fourWord_energy,fourSelectedRows_reference _ ((fourWord_reference_couple_normal w).mp hc)]
    split_ifs <;> norm_num

end Atlas.Rudvalis

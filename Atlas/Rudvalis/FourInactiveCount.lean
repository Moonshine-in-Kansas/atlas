import Atlas.Rudvalis.FourLiftCount

/-! Four-block supports avoiding a row: three normals, eight constants, 32 lifts. -/
namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary

theorem fourSupport_parameter_pair (v : FourSupportParameters) (p : Point) (x : E) :
    (fourSupportEquiv v).val (p,x)+(fourSupportEquiv v).val (p,x+p.val)=dot v.1.val p.val := by
  change (v.2.val.val p+dot (matrixAt (outerMatrix v.1.val v.1.val) p.val) x+theta p 0 x)+
    (v.2.val.val p+dot (matrixAt (outerMatrix v.1.val v.1.val) p.val) (x+p.val)+theta p 0 (x+p.val))=_
  simp only [matrixAt_outer,dot_smul_left,theta_zero_parameter,add_zero,dot_add_right]
  have h : ∀ e s t : Bit,(e+s*t)+(e+(s*t+s*s))=s := by decide +kernel
  exact h _ _ _

theorem fourSupport_parameter_row_zero (v : FourSupportParameters) (p : Point) :
    (∀x : E,(fourSupportEquiv v).val (p,x)=0) ↔ dot v.1.val p.val=0 := by
  constructor
  · intro h
    have hp := fourSupport_parameter_pair v p 0
    rw [h,h,zero_add] at hp
    exact hp.symm
  · intro h x
    change v.2.val.val p+dot (matrixAt (outerMatrix v.1.val v.1.val) p.val) x+theta p 0 x=0
    simp only [matrixAt_outer,h,zero_smul,theta_zero_parameter,add_zero]
    simpa [dot] using v.2.val.prop p h

theorem fourSupport_parameter_pair_zero (v : FourSupportParameters) (p : Point) (x : E) :
    ((fourSupportEquiv v).val (p,x)=0 ∧ (fourSupportEquiv v).val (p,x+p.val)=0) ↔
      dot v.1.val p.val=0 := by
  constructor
  · rintro ⟨h1,h2⟩
    have hp := fourSupport_parameter_pair v p x
    rw [h1,h2,zero_add] at hp
    exact hp.symm
  · intro h
    exact ⟨(fourSupport_parameter_row_zero v p).mpr h x,
      (fourSupport_parameter_row_zero v p).mpr h (x+p.val)⟩

abbrev FourInactiveSupports (p : Point) :=
  {d : {d : BinaryWord // admissibleFourSupport d} // ∀x : E,d.val (p,x)=0}

noncomputable def fourInactiveSupportEquiv (p : Point) :
    FourInactiveSupports p ≃ Σ a : {a : Point // dot a.val p.val=0},OddActiveConstants a.val :=
  (Equiv.subtypeEquiv fourSupportEquiv (fun v => (fourSupport_parameter_row_zero v p).symm)).symm.trans
    (Equiv.subtypeSigmaEquiv OddActiveConstants (fun a : Point => dot a.val p.val=0))

theorem point_annihilator_card (p : Point) : Nat.card {a : Point // dot a.val p.val=0}=3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel +revert

theorem fourInactiveSupport_card (p : Point) : Nat.card (FourInactiveSupports p)=24 := by
  classical
  rw [Nat.card_congr (fourInactiveSupportEquiv p),Nat.card_sigma]
  simp only [oddActiveConstants_card,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,point_annihilator_card]

abbrev FourInactiveWords (p : Point) :=
  {w : FourMinimumWords // ∀x : E,reduce w.val.val (p,x)=0}

noncomputable def fourInactiveWordsEquiv (p : Point) :
    FourInactiveWords p ≃ Σ d : FourInactiveSupports p,minimumLift d.val.val :=
  (Equiv.subtypeEquiv fourMinimumWordsEquiv (fun _ => Iff.rfl)).trans
    (Equiv.subtypeSigmaEquiv (fun d : {d : BinaryWord // admissibleFourSupport d} => minimumLift d.val)
      (fun d => ∀x : E,d.val (p,x)=0))

theorem fourInactiveWords_card (p : Point) : Nat.card (FourInactiveWords p)=768 := by
  classical
  rw [Nat.card_congr (fourInactiveWordsEquiv p),Nat.card_sigma]
  simp_rw [four_minimum_fibre_card _ (Subtype.prop _)]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,fourInactiveSupport_card]

end Atlas.Rudvalis

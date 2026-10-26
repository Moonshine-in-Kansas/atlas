import Atlas.LinearGroups.ReeF4.SpecialNegativeA2Chart
import Atlas.LinearGroups.ReeF4.SpecialThirdPivot
import Atlas.LinearGroups.ReeF4.SpecialLeadingReductionFramework

/-! The chart24 recurrence through actual pivot words. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem positiveC3_reverse_apply {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (a : F) (u : TraceZero F) :
    ((negativeA2ChartWord hcard a)⁻¹).val u =
      longSL2Equiv a (theta F m a) ((weylSigma (F := F)) u) := by
  have hL : (longSL2Equiv a (theta F m a))⁻¹=longSL2Equiv a (theta F m a) := by
    apply inv_eq_of_mul_eq_one_left
    simp only [longSL2Equiv_mul,CharTwo.add_self_eq_zero,longSL2Equiv_zero]
  have hS : (weylSigma (F := F))⁻¹=weylSigma := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using weylSigma_square (F := F)
  change ((weylSigma (F := F))*longSL2Equiv a (theta F m a))⁻¹ u = _
  rw [mul_inv_rev,hL,hS]
  rfl

/-- Only the six needed coordinates; the abstract input keeps reduction small. -/
private theorem positiveC3_reverse_coordinates {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (a : F) (u : TraceZero F) :
    let w := ((negativeA2ChartWord hcard a)⁻¹).val u
    w.val.2 0 7=u.val.2 2 7 ∧
    w.val.2 2 7=u.val.2 0 7+a*u.val.2 2 7 ∧
    w.val.2 1 7=u.val.2 1 7 ∧
    w.val.2 1 6=u.val.2 1 5 ∧
    w.val.2 2 6=u.val.2 0 5 ∧
    w.val.2 2 5=u.val.2 0 6+theta F m a*u.val.2 0 5 := by
  dsimp only
  rw [positiveC3_reverse_apply]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem chart24_upper_indices : ∀ j : Fin 26,
    specialAbsoluteGrade 24 < specialAbsoluteGrade j →
      j=9 ∨ j=16 ∨ j=17 ∨ j=25 := by decide

private theorem chart7_allowed_upper_indices : ∀ j : Fin 26,
    allowedSpecialLeadingRoot j → specialAbsoluteGrade 7 < specialAbsoluteGrade j →
      j=9 ∨ j=24 ∨ j=25 := by
  unfold allowedSpecialLeadingRoot
  decide

private theorem normalizedChart24_of_raw {m : ℕ} {u : TraceZero F}
    (hu : IsSpecialVector m u) (hn : u.val.2 2 6=1)
    (h9 : u.val.2 0 7=0) (h16 : u.val.2 1 6=0)
    (h17 : u.val.2 1 7=0) (h25 : u.val.2 2 7=0) :
    IsSpecialVector m u ∧ isotropyCoordinates u 24=1 ∧
      ∀ j, specialAbsoluteGrade 24<specialAbsoluteGrade j → isotropyCoordinates u j=0 := by
  refine ⟨hu,hn,?_⟩
  intro j hj
  rcases chart24_upper_indices j hj with rfl|rfl|rfl|rfl
  · exact h9
  · exact h16
  · exact h17
  · exact h25

private theorem normalizedChart7_of_raw {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) {u : TraceZero F}
    (hu : IsSpecialVector m u) (hn : u.val.2 0 5=1)
    (h9 : u.val.2 0 7=0) (h24 : u.val.2 2 6=0) (h25 : u.val.2 2 7=0) :
    IsSpecialVector m u ∧ isotropyCoordinates u 7=1 ∧
      ∀ j, specialAbsoluteGrade 7<specialAbsoluteGrade j → isotropyCoordinates u j=0 := by
  refine ⟨hu,hn,hu.support_bound_of_allowed hcard 7 ?_⟩
  intro j hj hg
  rcases chart7_allowed_upper_indices j hj hg with rfl|rfl|rfl
  · exact h9
  · exact h24
  · exact h25

def positiveC3ChartEncode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F × NormalizedSpecialChart (F := F) m 7) : NormalizedSpecialChart (F := F) m 24 :=
  ⟨((negativeA2ChartWord hcard p.1)⁻¹).val p.2.val,by
    obtain ⟨h9,h25,h17,h16,hn,hpar⟩ := positiveC3_reverse_coordinates hcard p.1 p.2.val
    have hz9 : p.2.val.val.2 0 7=0 := p.2.property.2.2 9 (by decide)
    have hz25 : p.2.val.val.2 2 7=0 := p.2.property.2.2 25 (by decide)
    have hz17 : p.2.val.val.2 1 7=0 := p.2.property.2.2 17 (by decide)
    have hz15 : p.2.val.val.2 1 5=0 := p.2.property.2.2 15 (by decide)
    exact normalizedChart24_of_raw (p.2.property.1.map_model ((negativeA2ChartWord hcard p.1)⁻¹))
      (hn.trans p.2.property.2.1) (h9.trans hz25) (h16.trans hz15) (h17.trans hz17)
      (h25.trans (by rw [hz9,hz25,mul_zero,add_zero]))⟩

def positiveC3ChartParameter {m : ℕ} (u : NormalizedSpecialChart (F := F) m 24) : F :=
  thirdPivotParameter m u.val

theorem positiveC3ChartParameter_encode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F × NormalizedSpecialChart (F := F) m 7) :
    positiveC3ChartParameter (positiveC3ChartEncode hcard p)=p.1 := by
  obtain ⟨_,_,_,_,hn,hpar⟩ := positiveC3_reverse_coordinates hcard p.1 p.2.val
  have hz8 : p.2.val.val.2 0 6=0 := p.2.property.2.2 8 (by decide)
  have hn7 : p.2.val.val.2 0 5=1 := p.2.property.2.1
  change thetaInv F m (_ / _) = p.1
  dsimp only [positiveC3ChartEncode]
  rw [hpar,hn,hz8,hn7,mul_one,zero_add,div_one,thetaInv_theta hcard]

def positiveC3ChartDecode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : NormalizedSpecialChart (F := F) m 24) : F × NormalizedSpecialChart (F := F) m 7 :=
  (positiveC3ChartParameter u,⟨(thirdPivotDescent hcard u.val).val u.val,by
    have hc : u.val.val.2 2 6≠0 := by
      have h : u.val.val.2 2 6=1 := u.property.2.1
      rw [h]; exact one_ne_zero
    obtain ⟨hs,h9,h25,h17,h16,h24,h15,h8,he,hn⟩ := specialVector_C3_strict_descent hcard u.property.1
      (u.property.2.2 9 (by decide)) (u.property.2.2 25 (by decide))
      (u.property.2.2 16 (by decide)) (u.property.2.2 17 (by decide)) hc
    exact normalizedChart7_of_raw hcard hs (he.trans u.property.2.1) h9 h24 h25⟩)

private theorem positiveC3ChartDecode_lower {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : NormalizedSpecialChart (F := F) m 24) :
    (positiveC3ChartDecode hcard u).2.val=
      (negativeA2ChartWord hcard (positiveC3ChartParameter u)).val u.val := by
  have he : thirdPivotDescent hcard u.val =
      negativeA2ChartWord hcard (positiveC3ChartParameter u) := by
    apply Subtype.ext
    rfl
  dsimp only [positiveC3ChartDecode]
  rw [he]

def normalizedChart24Equiv {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    NormalizedSpecialChart (F := F) m 24 ≃ F × NormalizedSpecialChart (F := F) m 7 where
  toFun := positiveC3ChartDecode hcard
  invFun := positiveC3ChartEncode hcard
  left_inv u := by
    apply Subtype.ext
    change ((negativeA2ChartWord hcard (positiveC3ChartParameter u))⁻¹).val
      ((positiveC3ChartDecode hcard u).2.val)=u.val
    rw [positiveC3ChartDecode_lower]
    exact (negativeA2ChartWord hcard (positiveC3ChartParameter u)).val.symm_apply_apply u.val
  right_inv p := by
    apply Prod.ext
    · exact positiveC3ChartParameter_encode hcard p
    · apply Subtype.ext
      rw [positiveC3ChartDecode_lower,positiveC3ChartParameter_encode]
      change (negativeA2ChartWord hcard p.1).val (positiveC3ChartEncode hcard p).val = p.2.val
      have hv : (positiveC3ChartEncode hcard p).val =
          ((negativeA2ChartWord hcard p.1)⁻¹).val p.2.val := rfl
      rw [hv]
      exact chart_model_apply_inv (negativeA2ChartWord hcard p.1) p.2.val

theorem card_normalizedChart24_step {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (NormalizedSpecialChart (F := F) m 24)=
      Nat.card F * Nat.card (NormalizedSpecialChart (F := F) m 7) := by
  rw [Nat.card_congr (normalizedChart24Equiv hcard),Nat.card_prod]

end Atlas.ReeF4

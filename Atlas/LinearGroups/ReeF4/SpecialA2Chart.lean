import Atlas.LinearGroups.ReeF4.SpecialNegativeA2Chart
import Atlas.LinearGroups.ReeF4.SpecialFifthPivot
import Atlas.LinearGroups.ReeF4.SpecialLeadingExistence
import Atlas.LinearGroups.ReeF4.AlternatingRootWordCoordinates

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def A2ChartWord {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (p : F×F) : Model F m :=
  negativeC3ChartWord hcard p

def A2ChartInverseFormula (m : ℕ) (a b : F) (w : Carrier F) : Carrier F :=
  shortRootParameterFormula (theta F m).toRingHom a
    (shortRootCenterFormula (theta F m).toRingHom (b+a*theta F m a)
      (carrierPermute weylRhoPermutation w))

theorem A2ChartWord_inverse_formula {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F×F) (z : TraceZero F) :
    (((A2ChartWord hcard p)⁻¹).val z).val=A2ChartInverseFormula m p.1 p.2 z.val := by
  have hrho : (weylRho (F := F))⁻¹=weylRho := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using weylRho_square (F := F)
  change (((shortRootPairEquiv m hcard p.1 p.2)⁻¹ * (weylRho (F := F))⁻¹) z).val=_
  rw [hrho,shortRootPairEquiv_inv]
  change shortRootParameterFormula _ p.1
    (shortRootCenterFormula _ (p.2+p.1*theta F m p.1) (weylRho z).val)=_
  rw [coordinateCompatible_val weylRho_coordinateCompatible]
  rfl

private theorem A2Chart_forward_package {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (w : TraceZero F) (hs : IsSpecialVector m w) (h4 : w.val.2 0 2=1)
    (h7 : w.val.2 0 5=0) (h9 : w.val.2 0 7=0)
    (h24 : w.val.2 2 6=0) (h25 : w.val.2 2 7=0) :
    IsSpecialVector m w ∧ isotropyCoordinates w 4=1 ∧
      ∀ j, specialAbsoluteGrade 4<specialAbsoluteGrade j → isotropyCoordinates w j=0 := by
  refine ⟨hs,h4,?_⟩
  obtain ⟨r,hr,hne,habove⟩ := hs.exists_allowed_leading_root hcard
  have hb : ∀ r : Fin 26, allowedSpecialLeadingRoot r →
      r=7 ∨ r=9 ∨ r=24 ∨ r=25 ∨ specialAbsoluteGrade r≤specialAbsoluteGrade 4 := by
    unfold allowedSpecialLeadingRoot
    decide
  have hg : specialAbsoluteGrade r≤specialAbsoluteGrade 4 := by
    rcases hb r hr with rfl | rfl | rfl | rfl | h
    · exact (hne h7).elim
    · exact (hne h9).elim
    · exact (hne h24).elim
    · exact (hne h25).elim
    · exact h
  intro j hj
  exact habove j (lt_of_le_of_lt hg hj)

private theorem A2Chart_forward {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : NormalizedSpecialChart (F := F) m 7) :
    let z := (fifthPivotDescent hcard u.val).val u.val
    IsSpecialVector m z ∧ isotropyCoordinates z 4=1 ∧
      ∀ j, specialAbsoluteGrade 4<specialAbsoluteGrade j → isotropyCoordinates z j=0 := by
  have hn : u.val.val.2 0 5 ≠ 0 := by
    have he : u.val.val.2 0 5=1 := u.property.2.1
    rw [he]; exact one_ne_zero
  obtain ⟨hs,h9,h25,h17,h16,h24,h15,h8,h23,h7,h21,h14,hD0,hD1,h4,hn4⟩ :=
    specialVector_A2_strict_descent hcard u.property.1
      (u.property.2.2 9 (by decide)) (u.property.2.2 25 (by decide))
      (u.property.2.2 17 (by decide)) (u.property.2.2 16 (by decide))
      (u.property.2.2 24 (by decide)) (u.property.2.2 15 (by decide))
      (u.property.2.2 8 (by decide)) (u.property.2.2 23 (by decide)) hn
  exact A2Chart_forward_package hcard ((fifthPivotDescent hcard u.val).val u.val) hs (h4.trans u.property.2.1) h7 h9 h24 h25

/-- Coordinate algebra is normalized only on an abstract carrier. -/
private theorem A2Chart_carrier_coordinates (m : ℕ) (a b : F) (w : Carrier F)
    (hn : w.2 0 2=1) (ht : w.1 2=0)
    (hz0 : w.1 1=0) (hz1 : w.1 0=0) (hz5 : w.2 0 3=0) (hz6 : w.2 0 4=0) (hz7 : w.2 0 5=0) (hz8 : w.2 0 6=0) (hz9 : w.2 0 7=0) (hz13 : w.2 1 3=0) (hz14 : w.2 1 4=0) (hz15 : w.2 1 5=0) (hz16 : w.2 1 6=0) (hz17 : w.2 1 7=0) (hz21 : w.2 2 3=0) (hz22 : w.2 2 4=0) (hz23 : w.2 2 5=0) (hz24 : w.2 2 6=0) (hz25 : w.2 2 7=0) :
    let v := A2ChartInverseFormula m a b w
    v.2 0 5=1 ∧ v.2 0 4=theta F m a ∧ v.1 1=b ∧ v.2 0 6=0 ∧ v.2 0 7=0 ∧ v.2 1 5=0 ∧ v.2 1 6=0 ∧ v.2 1 7=0 ∧ v.2 2 5=0 ∧ v.2 2 6=0 ∧ v.2 2 7=0 := by
  dsimp only
  repeat' constructor
  all_goals simp [A2ChartInverseFormula,carrierPermute,weylRhoPermutation,weylRhoIndex,
    wilsonCoordinatesEquiv,shortRootParameterFormula,shortRootCenterFormula,
    hn,ht,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]

private theorem A2Chart_upper_indices : ∀ j : Fin 26,
    specialAbsoluteGrade 7 < specialAbsoluteGrade j →
    j=8 ∨ j=9 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=23 ∨ j=24 ∨ j=25 := by decide

private theorem A2Chart_inverse_raw_package (m : ℕ) (u : TraceZero F) (a b : F)
    (hn : u.val.2 0 5=1) (ha : u.val.2 0 4=theta F m a) (hb : u.val.1 1=b)
    (h8 : u.val.2 0 6=0) (h9 : u.val.2 0 7=0) (h15 : u.val.2 1 5=0) (h16 : u.val.2 1 6=0) (h17 : u.val.2 1 7=0) (h23 : u.val.2 2 5=0) (h24 : u.val.2 2 6=0) (h25 : u.val.2 2 7=0) :
    isotropyCoordinates u 7=1 ∧ u.val.2 0 4=theta F m a ∧ u.val.1 1=b ∧
      ∀ j, specialAbsoluteGrade 7<specialAbsoluteGrade j → isotropyCoordinates u j=0 := by
  refine ⟨hn,ha,hb,?_⟩
  intro j hj
  rcases A2Chart_upper_indices j hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h8
  · exact h9
  · exact h15
  · exact h16
  · exact h17
  · exact h23
  · exact h24
  · exact h25

private theorem A2Chart_inverse_coordinates {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F×F) (z : NormalizedSpecialChart (F := F) m 4) :
    let w := ((A2ChartWord hcard p)⁻¹).val z.val
    isotropyCoordinates w 7=1 ∧ w.val.2 0 4=theta F m p.1 ∧ w.val.1 1=p.2 ∧
      ∀ j, specialAbsoluteGrade 7<specialAbsoluteGrade j → isotropyCoordinates w j=0 := by
  dsimp only
  have hn : z.val.val.2 0 2=1 := z.property.2.1
  have hz0 : z.val.val.1 1=0 := z.property.2.2 0 (by decide)
  have hz1 : z.val.val.1 0=0 := z.property.2.2 1 (by decide)
  have hz5 : z.val.val.2 0 3=0 := z.property.2.2 5 (by decide)
  have hz6 : z.val.val.2 0 4=0 := z.property.2.2 6 (by decide)
  have hz7 : z.val.val.2 0 5=0 := z.property.2.2 7 (by decide)
  have hz8 : z.val.val.2 0 6=0 := z.property.2.2 8 (by decide)
  have hz9 : z.val.val.2 0 7=0 := z.property.2.2 9 (by decide)
  have hz13 : z.val.val.2 1 3=0 := z.property.2.2 13 (by decide)
  have hz14 : z.val.val.2 1 4=0 := z.property.2.2 14 (by decide)
  have hz15 : z.val.val.2 1 5=0 := z.property.2.2 15 (by decide)
  have hz16 : z.val.val.2 1 6=0 := z.property.2.2 16 (by decide)
  have hz17 : z.val.val.2 1 7=0 := z.property.2.2 17 (by decide)
  have hz21 : z.val.val.2 2 3=0 := z.property.2.2 21 (by decide)
  have hz22 : z.val.val.2 2 4=0 := z.property.2.2 22 (by decide)
  have hz23 : z.val.val.2 2 5=0 := z.property.2.2 23 (by decide)
  have hz24 : z.val.val.2 2 6=0 := z.property.2.2 24 (by decide)
  have hz25 : z.val.val.2 2 7=0 := z.property.2.2 25 (by decide)
  have ht := z.val.property
  change z.val.val.1 0+z.val.val.1 1+z.val.val.1 2=0 at ht
  simp only [hz0,hz1,zero_add] at ht
  have hraw := A2Chart_carrier_coordinates m p.1 p.2 z.val.val hn ht hz0 hz1 hz5 hz6 hz7 hz8 hz9 hz13 hz14 hz15 hz16 hz17 hz21 hz22 hz23 hz24 hz25
  dsimp only at hraw
  rw [←A2ChartWord_inverse_formula hcard p z.val] at hraw
  obtain ⟨hnorm,ha,hb,hu8,hu9,hu15,hu16,hu17,hu23,hu24,hu25⟩ := hraw
  exact A2Chart_inverse_raw_package m (((A2ChartWord hcard p)⁻¹).val z.val) p.1 p.2 hnorm ha hb hu8 hu9 hu15 hu16 hu17 hu23 hu24 hu25

def A2ChartEncode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : (F×F) × NormalizedSpecialChart (F := F) m 4) : NormalizedSpecialChart (F := F) m 7 :=
  ⟨((A2ChartWord hcard p.1)⁻¹).val p.2.val,
    p.2.property.1.map_model ((A2ChartWord hcard p.1)⁻¹),
    (A2Chart_inverse_coordinates hcard p.1 p.2).1,
    (A2Chart_inverse_coordinates hcard p.1 p.2).2.2.2⟩

def A2ChartParameters {m : ℕ} (u : NormalizedSpecialChart (F := F) m 7) : F×F :=
  (fifthPivotA m u.val,fifthPivotB u.val)

private theorem A2ChartParameters_eq {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : NormalizedSpecialChart (F := F) m 7) (p : F×F)
    (ha : u.val.val.2 0 4=theta F m p.1) (hb : u.val.val.1 1=p.2) :
    A2ChartParameters u=p := by
  have hn : u.val.val.2 0 5=1 := u.property.2.1
  apply Prod.ext
  · change thetaInv F m (u.val.val.2 0 4 / u.val.val.2 0 5)=p.1
    rw [ha,hn,div_one,thetaInv_theta hcard]
  · change u.val.val.1 1 / u.val.val.2 0 5=p.2
    rw [hb,hn,div_one]

theorem A2ChartParameters_encode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : (F×F) × NormalizedSpecialChart (F := F) m 4) :
    A2ChartParameters (A2ChartEncode hcard p)=p.1 := by
  have h := A2Chart_inverse_coordinates hcard p.1 p.2
  have hv : (A2ChartEncode hcard p).val = ((A2ChartWord hcard p.1)⁻¹).val p.2.val := rfl
  apply A2ChartParameters_eq hcard (A2ChartEncode hcard p) p.1
  · rw [hv]
    exact h.2.1
  · rw [hv]
    exact h.2.2.1

def A2ChartDecode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : NormalizedSpecialChart (F := F) m 7) :
    (F×F) × NormalizedSpecialChart (F := F) m 4 :=
  (A2ChartParameters u,⟨(fifthPivotDescent hcard u.val).val u.val,A2Chart_forward hcard u⟩)

private theorem A2ChartDecode_lower {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : NormalizedSpecialChart (F := F) m 7) :
    (A2ChartDecode hcard u).2.val=(A2ChartWord hcard (A2ChartParameters u)).val u.val := by
  have he : fifthPivotDescent hcard u.val = A2ChartWord hcard (A2ChartParameters u) := by
    apply Subtype.ext
    rfl
  dsimp only [A2ChartDecode]
  rw [he]

/-- Actual A2 chart: two independent field parameters over the A−2 chart. -/
def normalizedChart7Equiv {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    NormalizedSpecialChart (F := F) m 7 ≃ (F×F) × NormalizedSpecialChart (F := F) m 4 where
  toFun := A2ChartDecode hcard
  invFun := A2ChartEncode hcard
  left_inv u := by
    apply Subtype.ext
    change ((A2ChartWord hcard (A2ChartParameters u))⁻¹).val
      ((A2ChartDecode hcard u).2.val)=u.val
    rw [A2ChartDecode_lower]
    exact (A2ChartWord hcard (A2ChartParameters u)).val.symm_apply_apply u.val
  right_inv p := by
    apply Prod.ext
    · exact A2ChartParameters_encode hcard p
    · apply Subtype.ext
      rw [A2ChartDecode_lower,A2ChartParameters_encode]
      have hv : (A2ChartEncode hcard p).val = ((A2ChartWord hcard p.1)⁻¹).val p.2.val := rfl
      rw [hv]
      exact chart_model_apply_inv (A2ChartWord hcard p.1) p.2.val

theorem card_normalizedChart7 {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (NormalizedSpecialChart (F := F) m 7)=(Nat.card F)^6 := by
  rw [Nat.card_congr (normalizedChart7Equiv hcard),Nat.card_prod,Nat.card_prod,card_normalizedChart4 hcard]
  ring
end Atlas.ReeF4

import Atlas.LinearGroups.ReeF4.SpecialNegativeC3Chart
import Atlas.LinearGroups.ReeF4.SpecialSecondPivotDescent
import Atlas.LinearGroups.ReeF4.RootSuzukiLeviExterior
import Atlas.LinearGroups.ReeF4.SpecialPositiveC3Chart
import Atlas.LinearGroups.ReeF4.SpecialA2Chart

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The C4 pivot is the same actual rho·U(a,b) word used on the negative
natural block, now restricted to the first natural four-space. -/
def c4ChartWord {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (p : F×F) : Model F m :=
  negativeC3ChartWord hcard p

private theorem c4ChartWord_inverse_apply {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F×F) (w : TraceZero F) :
    ((c4ChartWord hcard p)⁻¹).val w=
      shortRootPairEquiv m hcard p.1 (p.2+p.1*theta F m p.1) (weylRho w) := by
  have hrho : (weylRho (F := F))⁻¹=weylRho := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using weylRho_square (F := F)
  change ((weylRho (F := F)) * shortRootPairEquiv m hcard p.1 p.2)⁻¹ w=_
  rw [mul_inv_rev,hrho,shortRootPairEquiv_inv]
  rfl

private theorem chart24_naturalBlock {m : ℕ} (z : NormalizedSpecialChart (F := F) m 24) :
    suzukiLeviBlockProject 0 z.val=![0,0,0,1] := by
  funext i
  fin_cases i
  · exact z.property.2.2 25 (by decide)
  · exact z.property.2.2 17 (by decide)
  · exact z.property.2.2 16 (by decide)
  · exact z.property.2.1

/-- The full needed inverse parameter data comes from the already certified
four-dimensional restriction; no whole26-coordinate expansion is needed. -/
theorem c4ChartWord_inverse_block {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F×F) (z : NormalizedSpecialChart (F := F) m 24) :
    suzukiLeviBlockProject 0 (((c4ChartWord hcard p)⁻¹).val z.val)=
      ![1,p.1,p.2+p.1*theta F m p.1,
        p.1^2*theta F m p.1+p.1*(p.2+p.1*theta F m p.1)+theta F m (p.2+p.1*theta F m p.1)] := by
  rw [c4ChartWord_inverse_apply,shortRootPairEquiv_apply,shortRootPairLinear_suzukiBlock,
    weylRho_suzukiBlock,chart24_naturalBlock]
  funext i
  fin_cases i <;>
    simp [suzukiLeviRootMatrix,Atlas.SuzukiFamily.w,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem c4ChartWord_inverse_fixed {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F×F) (w : TraceZero F) :
    suzukiLeviFixedProject (((c4ChartWord hcard p)⁻¹).val w)=suzukiLeviFixedProject w := by
  rw [c4ChartWord_inverse_apply,shortRootPairEquiv_apply,shortRootPairLinear_suzukiFixed,
    weylRho_suzukiFixed]

private theorem c4_upper_package (w : TraceZero F) (h9 : w.val.2 0 7=0) :
    ∀ j, specialAbsoluteGrade 25<specialAbsoluteGrade j → isotropyCoordinates w j=0 := by
  have he : ∀ j : Fin 26, specialAbsoluteGrade 25 < specialAbsoluteGrade j → j=9 := by decide
  intro j hj
  have hj9 := he j hj
  subst j
  exact h9

private theorem c4_forward_package {m : ℕ} (w : TraceZero F)
    (hs : IsSpecialVector m w) (hn : w.val.2 2 6=1)
    (h9 : w.val.2 0 7=0) (h16 : w.val.2 1 6=0)
    (h17 : w.val.2 1 7=0) (h25 : w.val.2 2 7=0) :
    IsSpecialVector m w ∧ isotropyCoordinates w 24=1 ∧
      ∀ j, specialAbsoluteGrade 24<specialAbsoluteGrade j → isotropyCoordinates w j=0 := by
  refine ⟨hs,hn,?_⟩
  intro j hj
  have he : ∀ j : Fin 26, specialAbsoluteGrade 24 < specialAbsoluteGrade j →
      j=9 ∨ j=16 ∨ j=17 ∨ j=25 := by decide
  rcases he j hj with rfl | rfl | rfl | rfl
  · exact h9
  · exact h16
  · exact h17
  · exact h25

private theorem c4_fixed_raw (u v : TraceZero F)
    (h : suzukiLeviFixedProject u=suzukiLeviFixedProject v) :
    u.val.2 0 7=v.val.2 0 7 := congrFun h 3

private theorem c4_block_raw (m : ℕ) (u : TraceZero F) (p : F×F)
    (h : suzukiLeviBlockProject 0 u=
      ![1,p.1,p.2+p.1*theta F m p.1,
        p.1^2*theta F m p.1+p.1*(p.2+p.1*theta F m p.1)+theta F m (p.2+p.1*theta F m p.1)]) :
    u.val.2 2 7=1 ∧ u.val.2 1 7=p.1 ∧ u.val.2 1 6=p.2+p.1*theta F m p.1 := by
  exact ⟨congrFun h 0,congrFun h 1,congrFun h 2⟩

private def c4_encode_raw_package {m : ℕ} (u : TraceZero F)
    (hs : IsSpecialVector m u) (hn : u.val.2 2 7=1)
    (hz : ∀ j, specialAbsoluteGrade 25<specialAbsoluteGrade j → isotropyCoordinates u j=0) :
    NormalizedSpecialChart (F := F) m 25 := ⟨u,hs,hn,hz⟩

private theorem c4ChartWord_inverse_upper {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F×F) (z : NormalizedSpecialChart (F := F) m 24) :
    ∀ j, specialAbsoluteGrade 25<specialAbsoluteGrade j →
      isotropyCoordinates (((c4ChartWord hcard p)⁻¹).val z.val) j=0 := by
  have hfixed := c4_fixed_raw (((c4ChartWord hcard p)⁻¹).val z.val) z.val
    (c4ChartWord_inverse_fixed hcard p z.val)
  have hz : z.val.val.2 0 7=0 := z.property.2.2 9 (by decide)
  have hA : (((c4ChartWord hcard p)⁻¹).val z.val).val.2 0 7=0 := hfixed.trans hz
  exact c4_upper_package (((c4ChartWord hcard p)⁻¹).val z.val) hA

def c4ChartEncode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : (F×F) × NormalizedSpecialChart (F := F) m 24) : NormalizedSpecialChart (F := F) m 25 :=
  c4_encode_raw_package (((c4ChartWord hcard p.1)⁻¹).val p.2.val)
    (p.2.property.1.map_model ((c4ChartWord hcard p.1)⁻¹))
    (c4_block_raw m (((c4ChartWord hcard p.1)⁻¹).val p.2.val) p.1
      (c4ChartWord_inverse_block hcard p.1 p.2)).1
    (c4ChartWord_inverse_upper hcard p.1 p.2)

def c4ChartParameters {m : ℕ} (u : NormalizedSpecialChart (F := F) m 25) : F×F :=
  (secondPivotA u.val,secondPivotB m u.val)

private theorem c4_parameters_of_raw {m : ℕ}
    (u : NormalizedSpecialChart (F := F) m 25) (p : F×F)
    (h1 : u.val.val.2 1 7=p.1)
    (h2 : u.val.val.2 1 6=p.2+p.1*theta F m p.1) : c4ChartParameters u=p := by
  have h0 : u.val.val.2 2 7=1 := u.property.2.1
  apply Prod.ext
  · change u.val.val.2 1 7/u.val.val.2 2 7=p.1
    rw [h0,h1,div_one]
  · change (u.val.val.2 1 6+theta F m (u.val.val.2 1 7/u.val.val.2 2 7)*u.val.val.2 1 7)/u.val.val.2 2 7=p.2
    simp only [h0,h1,h2,div_one]
    linear_combination (p.1*theta F m p.1)*(CharTwo.two_eq_zero (R := F))

theorem c4ChartParameters_encode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : (F×F) × NormalizedSpecialChart (F := F) m 24) :
    c4ChartParameters (c4ChartEncode hcard p)=p.1 := by
  have hraw := c4_block_raw m (((c4ChartWord hcard p.1)⁻¹).val p.2.val) p.1
    (c4ChartWord_inverse_block hcard p.1 p.2)
  have hv : (c4ChartEncode hcard p).val = ((c4ChartWord hcard p.1)⁻¹).val p.2.val := rfl
  apply c4_parameters_of_raw (c4ChartEncode hcard p) p.1
  · rw [hv]
    exact hraw.2.1
  · rw [hv]
    exact hraw.2.2

def c4ChartDecode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : NormalizedSpecialChart (F := F) m 25) :
    (F×F) × NormalizedSpecialChart (F := F) m 24 :=
  (c4ChartParameters u,⟨(secondPivotDescent hcard u.val).val u.val,by
    have hc : u.val.val.2 2 7≠0 := by
      have he : u.val.val.2 2 7=1 := u.property.2.1
      rw [he]; exact one_ne_zero
    obtain ⟨hs,h9,h25,h17,h16,he,hn⟩ := specialVector_C4_descent hcard u.property.1
      (u.property.2.2 9 (by decide)) hc
    exact c4_forward_package ((secondPivotDescent hcard u.val).val u.val) hs (he.trans u.property.2.1) h9 h16 h17 h25⟩)

private theorem c4ChartDecode_lower {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : NormalizedSpecialChart (F := F) m 25) :
    (c4ChartDecode hcard u).2.val=(c4ChartWord hcard (c4ChartParameters u)).val u.val := by
  have hw : c4ChartWord hcard (c4ChartParameters u)=secondPivotDescent hcard u.val := by
    apply Subtype.ext
    rfl
  dsimp only [c4ChartDecode]
  rw [hw]

def normalizedChart25Equiv {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    NormalizedSpecialChart (F := F) m 25 ≃ (F×F) × NormalizedSpecialChart (F := F) m 24 where
  toFun := c4ChartDecode hcard
  invFun := c4ChartEncode hcard
  left_inv u := by
    apply Subtype.ext
    have hp : (c4ChartDecode hcard u).1=c4ChartParameters u := rfl
    have hv : (c4ChartEncode hcard (c4ChartDecode hcard u)).val=
        ((c4ChartWord hcard (c4ChartDecode hcard u).1)⁻¹).val (c4ChartDecode hcard u).2.val := rfl
    rw [hv,hp,c4ChartDecode_lower]
    exact (c4ChartWord hcard (c4ChartParameters u)).val.symm_apply_apply u.val
  right_inv p := by
    apply Prod.ext
    · exact c4ChartParameters_encode hcard p
    · apply Subtype.ext
      rw [c4ChartDecode_lower,c4ChartParameters_encode]
      have hv : (c4ChartEncode hcard p).val=((c4ChartWord hcard p.1)⁻¹).val p.2.val := rfl
      rw [hv]
      exact chart_model_apply_inv (c4ChartWord hcard p.1) p.2.val

theorem card_normalizedChart25_step {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (NormalizedSpecialChart (F := F) m 25)=
      (Nat.card F)^2 * Nat.card (NormalizedSpecialChart (F := F) m 24) := by
  rw [Nat.card_congr (normalizedChart25Equiv hcard),Nat.card_prod,Nat.card_prod,pow_two]

theorem card_normalizedChart25 {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (NormalizedSpecialChart (F := F) m 25)=(Nat.card F)^9 := by
  rw [card_normalizedChart25_step hcard,card_normalizedChart24_step hcard,card_normalizedChart7 hcard]
  ring
end Atlas.ReeF4


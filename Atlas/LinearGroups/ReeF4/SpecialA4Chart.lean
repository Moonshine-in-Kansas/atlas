import Atlas.LinearGroups.ReeF4.SpecialC4Chart
import Atlas.LinearGroups.ReeF4.SpecialPointPivot

/-! Final normalized chart. Inverse coordinates are recovered from the already
proved two forward coefficient identities and abstract group cancellation;
no concrete inverse matrix is expanded. -/
noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def a4ChartWord {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (a : F) : Model F m :=
  ⟨highestPivotRaw a (theta F m a),
    (modelSubgroup F m).mul_mem (weylOperator_mem_modelSubgroup m 1)
      (longSL2Parameter_mem_modelSubgroup hcard a)⟩

private theorem a4Chart_apply_inv {m : ℕ} (g : Model F m) (u : TraceZero F) :
    g.val ((g⁻¹).val u)=u := g.val.apply_symm_apply u
private theorem a4Chart_inv_apply {m : ℕ} (g : Model F m) (u : TraceZero F) :
    (g⁻¹).val (g.val u)=u := g.val.symm_apply_apply u

theorem a4ChartWord_top {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (a : F) (w : TraceZero F) :
    ((a4ChartWord hcard a).val w).val.2 0 7=w.val.2 2 7+a*w.val.2 0 7 :=
  highestPivotRaw_top a (theta F m a) w

theorem a4ChartWord_next {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (a : F) (w : TraceZero F) :
    ((a4ChartWord hcard a).val w).val.2 2 7=w.val.2 0 7 :=
  highestPivotRaw_next a (theta F m a) w

private theorem a4Chart_highest_grade : ∀ j : Fin 26,
    specialAbsoluteGrade j≤specialAbsoluteGrade 9 := by decide
private theorem a4Chart_above_next : ∀ j : Fin 26,
    specialAbsoluteGrade 25<specialAbsoluteGrade j → j=9 := by decide

private theorem a4Chart_inverse_coordinates {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (a : F) (z : NormalizedSpecialChart (F := F) m 25) :
    let w := ((a4ChartWord hcard a)⁻¹).val z.val
    w.val.2 0 7=1 ∧ w.val.2 2 7=a := by
  let w := ((a4ChartWord hcard a)⁻¹).val z.val
  have hc := a4Chart_apply_inv (a4ChartWord hcard a) z.val
  have hnext := congrArg (fun v : TraceZero F => v.val.2 2 7) hc
  rw [a4ChartWord_next] at hnext
  have hn : w.val.2 0 7=1 := hnext.trans z.property.2.1
  have htop := congrArg (fun v : TraceZero F => v.val.2 0 7) hc
  rw [a4ChartWord_top] at htop
  have hz : z.val.val.2 0 7=0 := z.property.2.2 9 (by decide)
  change w.val.2 2 7+a*w.val.2 0 7=z.val.val.2 0 7 at htop
  rw [hn,hz,mul_one] at htop
  refine ⟨hn,?_⟩
  calc
    w.val.2 2 7 = w.val.2 2 7+(a+a) := by rw [CharTwo.add_self_eq_zero,add_zero]
    _ = (w.val.2 2 7+a)+a := by rw [add_assoc]
    _ = a := by rw [htop,zero_add]

private def a4_encode_raw_package {m : ℕ} (u : TraceZero F)
    (hs : IsSpecialVector m u) (hn : u.val.2 0 7=1) :
    NormalizedSpecialChart (F := F) m 9 :=
  ⟨u,hs,hn,fun j hj => False.elim ((not_lt_of_ge (a4Chart_highest_grade j)) hj)⟩

private def a4_decode_raw_package {m : ℕ} (u : TraceZero F)
    (hs : IsSpecialVector m u) (hn : u.val.2 2 7=1) (hz : u.val.2 0 7=0) :
    NormalizedSpecialChart (F := F) m 25 :=
  ⟨u,hs,hn,by
    intro j hj
    have he := a4Chart_above_next j hj
    subst j
    exact hz⟩

def a4ChartEncode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F × NormalizedSpecialChart (F := F) m 25) : NormalizedSpecialChart (F := F) m 9 :=
  a4_encode_raw_package (((a4ChartWord hcard p.1)⁻¹).val p.2.val)
    (p.2.property.1.map_model ((a4ChartWord hcard p.1)⁻¹))
    (a4Chart_inverse_coordinates hcard p.1 p.2).1

def a4ChartParameter {m : ℕ} (u : NormalizedSpecialChart (F := F) m 9) : F :=
  highestPivotParameter u.val

private theorem a4_parameter_of_raw {m : ℕ}
    (u : NormalizedSpecialChart (F := F) m 9) (a : F)
    (hc : u.val.val.2 2 7=a) : a4ChartParameter u=a := by
  have hn : u.val.val.2 0 7=1 := u.property.2.1
  change u.val.val.2 2 7/u.val.val.2 0 7=a
  rw [hc,hn,div_one]

theorem a4ChartParameter_encode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F × NormalizedSpecialChart (F := F) m 25) :
    a4ChartParameter (a4ChartEncode hcard p)=p.1 := by
  exact a4_parameter_of_raw (a4ChartEncode hcard p) p.1
    (a4Chart_inverse_coordinates hcard p.1 p.2).2

private theorem a4ChartWord_parameter_eq {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : NormalizedSpecialChart (F := F) m 9) :
    a4ChartWord hcard (a4ChartParameter u)=highestPivotModel hcard u.val := by
  apply Subtype.ext
  rfl

private theorem a4ChartWord_parameter_top {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (u : NormalizedSpecialChart (F := F) m 9) :
    ((a4ChartWord hcard (a4ChartParameter u)).val u.val).val.2 0 7=0 := by
  rw [a4ChartWord_parameter_eq]
  apply highestPivot_top_eq_zero
  have hn : u.val.val.2 0 7=1 := u.property.2.1
  rw [hn]
  exact one_ne_zero

def a4ChartDecode {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : NormalizedSpecialChart (F := F) m 9) :
    F × NormalizedSpecialChart (F := F) m 25 :=
  (a4ChartParameter u,
    a4_decode_raw_package ((a4ChartWord hcard (a4ChartParameter u)).val u.val)
      (u.property.1.map_model (a4ChartWord hcard (a4ChartParameter u)))
      ((a4ChartWord_next hcard (a4ChartParameter u) u.val).trans u.property.2.1)
      (a4ChartWord_parameter_top hcard u))

/-- Exact recurrence for the final affine chart, with its own recovered parameter. -/
def normalizedChart9Equiv {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    NormalizedSpecialChart (F := F) m 9 ≃ F × NormalizedSpecialChart (F := F) m 25 where
  toFun := a4ChartDecode hcard
  invFun := a4ChartEncode hcard
  left_inv u := by
    apply Subtype.ext
    have hp : (a4ChartDecode hcard u).1 = a4ChartParameter u := rfl
    have hv : (a4ChartEncode hcard (a4ChartDecode hcard u)).val =
        ((a4ChartWord hcard (a4ChartDecode hcard u).1)⁻¹).val (a4ChartDecode hcard u).2.val := rfl
    have hd : (a4ChartDecode hcard u).2.val =
        (a4ChartWord hcard (a4ChartParameter u)).val u.val := rfl
    rw [hv,hp,hd]
    exact a4Chart_inv_apply (a4ChartWord hcard (a4ChartParameter u)) u.val
  right_inv p := by
    apply Prod.ext
    · exact a4ChartParameter_encode hcard p
    · apply Subtype.ext
      have hd : (a4ChartDecode hcard (a4ChartEncode hcard p)).2.val =
          (a4ChartWord hcard (a4ChartParameter (a4ChartEncode hcard p))).val
            (a4ChartEncode hcard p).val := rfl
      have hv : (a4ChartEncode hcard p).val = ((a4ChartWord hcard p.1)⁻¹).val p.2.val := rfl
      rw [hd,a4ChartParameter_encode,hv]
      exact a4Chart_apply_inv (a4ChartWord hcard p.1) p.2.val

theorem card_normalizedChart9_recurrence {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (NormalizedSpecialChart (F := F) m 9)=
      Nat.card F * Nat.card (NormalizedSpecialChart (F := F) m 25) := by
  rw [Nat.card_congr (normalizedChart9Equiv hcard),Nat.card_prod]

end Atlas.ReeF4

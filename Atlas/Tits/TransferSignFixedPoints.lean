import Atlas.Tits.TransferWitnessPowers
import Atlas.Rudvalis.HeavyCrossScalarRigidity
import Atlas.Rudvalis.FourCrossLabels

/-! Fixed points of alpha²=E₃ on the actual orthogonal shell. The proof uses
the three geometric minimum-vector types, not enumeration of 1755 crosses. -/

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary
set_option maxRecDepth 16384

/-- A nonzero Fano linear form constant on another form's four active rows
must be that form itself. This is a seven-point linear-algebra certificate. -/
theorem active_rows_constant_sign (a : Point) (b : Bit)
    (h : ∀ p : Point, dot a.val p.val = 1 → dot (binaryLabel 3) p.val = b) :
    a.val = binaryLabel 3 := by
  decide +kernel +revert

theorem signE3_ne_one : seedARowSign (binaryLabel 3) ≠ 1 := by
  intro h
  have he := congrArg
    (fun g : codeGroup => g.val.left.toAdd (rowLabel 1,0)) h
  change (1 : Bit) = 0 at he
  exact one_ne_zero he

theorem signE3_ne_negative : seedARowSign (binaryLabel 3) ≠ codeI^2 := by
  intro h
  have hi : (codeI^2).val = negativeMonomial := by
    rw [Subgroup.coe_pow,pow_two]
    exact codeI_squared_signed
  have he := congrArg
    (fun g : codeGroup => g.val.left.toAdd (rowLabel 4,0)) h
  rw [hi] at he
  change (0 : Bit) = 1 at he
  exact zero_ne_one he

/-- A positive sign eigenvector can be nonzero only on positive rows. -/
theorem sign_fixed_nonzero_row (a : E) (v : MinimalShell)
    (hv : seedARowSign a • v = v) (p : Point) (x : E)
    (hx : v.val.val (p,x) ≠ 0) : dot a p.val = 0 := by
  have he := congrArg (fun w : MinimalShell => w.val.val (p,x)) hv
  change liftedSign (dot a p.val) (v.val.val (p,x)) = v.val.val (p,x) at he
  by_contra hn
  simp only [liftedSign,hn,ite_false] at he
  exact hx (by linarith)

/-- A negative sign eigenvector can be nonzero only on negative rows. -/
theorem sign_negative_nonzero_row (a : E) (v : MinimalShell)
    (hv : seedARowSign a • v = (codeI^2) • v) (p : Point) (x : E)
    (hx : v.val.val (p,x) ≠ 0) : dot a p.val = 1 := by
  have hneg : ((codeI^2) • v).val.val = -v.val.val := by
    change rationalMonomialHom (codeI.val^2) v.val.val = -v.val.val
    rw [map_pow,pow_two,LinearEquiv.mul_apply]
    exact rationalI_square _
  have he := congrArg (fun w : MinimalShell => w.val.val (p,x)) hv
  change liftedSign (dot a p.val) (v.val.val (p,x)) = ((codeI^2) • v).val.val (p,x) at he
  rw [hneg] at he
  have hbit : ∀ b : Bit, b = 0 ∨ b = 1 := by decide +kernel
  rcases hbit (dot a p.val) with hz | ho
  · exfalso
    rw [hz] at he
    simp only [liftedSign,ite_true,Pi.neg_apply] at he
    exact hx (by linarith)
  · exact ho

/-- Every active row of a four-block minimum has a nonzero coordinate. -/
theorem four_word_active_row_nonzero (w : FourMinimumWords) (p : Point)
    (hp : dot (fourSupportNormal ⟨reduce w.val.val,w.prop.2⟩).val p.val = 1) :
    ∃ x : E, (minimumWordShellLift (fourMinimumWord w)).val.val (p,x) ≠ 0 := by
  classical
  have hn : ¬∀ x : E, reduce w.val.val (p,x) = 0 := by
    intro hz
    have horth := (fourWord_coordinate_orthogonal_iff w p 0).mpr hz
    have he := (fourWord_row_orthogonal_normal w p 0).mp horth
    rw [hp] at he
    exact one_ne_zero he
  obtain ⟨x,hx⟩ := not_forall.mp hn
  exact ⟨x,fun h => hx ((minimumWordShellLift_zero_iff (fourMinimumWord w) (p,x)).mp h)⟩

/-- Any four-block cross fixed by E₃ has label 3. -/
theorem signE3_fixed_four_label (w : FourMinimumWords)
    (hw : seedARowSign (binaryLabel 3) •
      minimalCross (minimumWordShellLift (fourMinimumWord w)) =
      minimalCross (minimumWordShellLift (fourMinimumWord w))) :
    (fourSupportNormal ⟨reduce w.val.val,w.prop.2⟩).val = binaryLabel 3 := by
  rcases code_sign_cross_phase (seedARowSign (binaryLabel 3)) rfl
    (minimumWordShellLift (fourMinimumWord w)) hw with hv | hv
  · apply active_rows_constant_sign _ 0
    intro p hp
    obtain ⟨x,hx⟩ := four_word_active_row_nonzero w p hp
    exact sign_fixed_nonzero_row _ _ hv p x hx
  · apply active_rows_constant_sign _ 1
    intro p hp
    obtain ⟨x,hx⟩ := four_word_active_row_nonzero w p hp
    exact sign_negative_nonzero_row _ _ hv p x hx

/-- A fixed four-block cross cannot be orthogonal to the reference cross. -/
theorem signE3_no_orthogonal_four (w : FourMinimumWords)
    (ho : CrossOrthogonal localReferenceCross
      (minimalCross (minimumWordShellLift (fourMinimumWord w)))) :
    seedARowSign (binaryLabel 3) • minimalCross (minimumWordShellLift (fourMinimumWord w)) ≠
      minimalCross (minimumWordShellLift (fourMinimumWord w)) := by
  intro hw
  have hl := signE3_fixed_four_label w hw
  rw [localReferenceCross_eq] at ho
  have he := (fourWord_row_orthogonal_normal w (rowLabel 0) 0).mp ho
  rw [hl] at he
  change (1 : Bit) = 0 at he
  exact one_ne_zero he

/-- The nonconstant row sign E₃ fixes no heavy cross. -/
theorem signE3_no_heavy (w : HeavyMinimumWords) :
    seedARowSign (binaryLabel 3) • minimalCross (minimumWordShellLift (heavyMinimumWord w)) ≠
      minimalCross (minimumWordShellLift (heavyMinimumWord w)) := by
  intro hw
  rcases code_sign_heavy_cross_scalar (seedARowSign (binaryLabel 3)) rfl w hw with h | h
  · exact signE3_ne_one h
  · exact signE3_ne_negative h

theorem signE3_fixed_orthogonal_iff (c : MinimalCross)
    (ho : CrossOrthogonal localReferenceCross c) :
    seedARowSign (binaryLabel 3) • c = c ↔ c ∈ coordinateFrame := by
  constructor
  · intro hc
    induction c using Quotient.inductionOn with
    | h v =>
      rcases minimalShell_piece_cases v with hcoord | hfour | hheavy
      · exact (minimalCross_mem_coordinateFrame v).mpr hcoord
      · obtain ⟨w,rfl⟩ := hfour
        exact False.elim (signE3_no_orthogonal_four w ho hc)
      · obtain ⟨w,rfl⟩ := hheavy
        exact False.elim (signE3_no_heavy w hc)
  · intro hc
    obtain ⟨i,rfl⟩ := coordinateFrame_rep c hc
    rw [coordinateCross_action]
    rfl

theorem pointE3_fixed_neighbour_iff (c : Neighbours) :
    codePointHom pointE3 • c = c ↔ c.val ∈ coordinateFrame := by
  constructor
  · intro h
    apply (signE3_fixed_orthogonal_iff c.val c.prop).mp
    exact congrArg (fun z : Neighbours => z.val) h
  · intro h
    apply Subtype.ext
    exact (signE3_fixed_orthogonal_iff c.val c.prop).mpr h

theorem localAlpha_square_fixed_iff (c : Neighbours) :
    localAlpha^2 • c = c ↔ c.val ∈ coordinateFrame := by
  rw [localAlpha_square]
  exact pointE3_fixed_neighbour_iff c

noncomputable def alphaSquareFixedEquiv :
    {c : Neighbours // localAlpha^2 • c = c} ≃
      {c : coordinateFrame // CrossOrthogonal localReferenceCross c.val} where
  toFun c := ⟨⟨c.val.val,(localAlpha_square_fixed_iff c.val).mp c.prop⟩,c.val.prop⟩
  invFun c := ⟨⟨c.val.val,c.prop⟩,(localAlpha_square_fixed_iff _).mpr c.val.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Precisely the 27 other coordinate crosses are fixed by alpha². -/
theorem localAlpha_square_fixed_card : Nat.card {c : Neighbours // localAlpha^2 • c = c} = 27 := by
  rw [Nat.card_congr alphaSquareFixedEquiv]
  exact coordinateFrame_orthogonal_card ⟨localReferenceCross,by
    rw [localReferenceCross_eq]
    exact coordinateCross_mem _⟩

end Atlas.Tits

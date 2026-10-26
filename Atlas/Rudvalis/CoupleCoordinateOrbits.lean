import Atlas.Rudvalis.CoupleFourSupportOrbit
import Atlas.Rudvalis.CoupleFusionGroup

namespace Atlas.Rudvalis
set_option maxRecDepth 16384

 theorem couple_other_row_translation (p : Point) (hp : p≠rowLabel 0) (x y : E) :
    ∃g : codeCoupleStabilizer,g.val • coordinateCross (p,x)=coordinateCross (p,y) := by
  have hc : ∀p q : Point,p≠q → ∃u : E,dot u q.val=0 ∧ dot u p.val=1 := by
    decide +kernel
  obtain ⟨u,hu0,hup⟩ := hc p (rowLabel 0) hp
  let B := outerMatrix (x+y) u
  have hB0 : matrixAt B (rowLabel 0).val=0 := by rw [matrixAt_outer,hu0,zero_smul]
  have hBp : matrixAt B p.val=x+y := by rw [matrixAt_outer,hup,one_smul]
  obtain ⟨g,hg⟩ := codePermutationHom_surjective ⟨coordinateTranslation B,coordinateTranslation_mem B⟩
  have hgr : g.val.right=coordinateTranslation B := congrArg Subtype.val hg
  have hfix (z : E) : g • coordinateCross (rowLabel 0,z)=coordinateCross (rowLabel 0,z) := by
    rw [coordinateCross_action,hgr]
    change coordinateCross (rowLabel 0,z+matrixAt B (rowLabel 0).val)=_
    rw [hB0,add_zero]
  refine ⟨⟨g,?_,?_⟩,?_⟩
  · change g • localReferenceCross=localReferenceCross
    rw [localReferenceCross_eq]; exact hfix _
  · change g • referenceSecondCross=referenceSecondCross
    rw [referenceSecondCross_eq]; exact hfix _
  · change g • coordinateCross (p,x)=_
    rw [coordinateCross_action,hgr]
    change coordinateCross (p,x+matrixAt B p.val)=_
    rw [hBp,←add_assoc,vector_add_self,zero_add]

 theorem coupleBeta_row_coordinate (r : Fin 7) (x : E) :
    (coupleCodeBeta.val.right (rowLabel r,x)).1=rowLabel (coupleBetaRow r) := by
  obtain ⟨k,hk⟩ := (seedInnerLabel_bijective r).surjective x
  let j := signedPositionIndex k
  have hj : signedPositionIndex j=k := by dsimp [j]; decide +kernel +revert
  have hz : originalCoordinateEquiv (r,j)=(rowLabel r,x) := by
    change (rowLabel r,seedInnerLabel r (signedPositionIndex j))=_
    rw [hj,hk]
  rw [←hz]
  exact coupleCodeBeta_row r j

 theorem coupleBeta_pow_row_coordinate (n : ℕ) (r : Fin 7) (x : E) :
    ((coupleCodeBeta^n).val.right (rowLabel r,x)).1=rowLabel ((coupleBetaRow^[n]) r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',Subgroup.coe_mul]
    change (coupleCodeBeta.val.right ((coupleCodeBeta^n).val.right (rowLabel r,x))).1=_
    have hz : (coupleCodeBeta^n).val.right (rowLabel r,x)=
      (rowLabel ((coupleBetaRow^[n]) r),((coupleCodeBeta^n).val.right (rowLabel r,x)).2) := Prod.ext ih rfl
    rw [hz,coupleBeta_row_coordinate,Function.iterate_succ_apply']

 theorem coupleBeta_other_row_connected (r s : Fin 7) (hr : r≠0) (hs : s≠0)
    (hclass : (r=4 ∨ r=5) ↔ (s=4 ∨ s=5)) :
    ∃n : Fin 4,(coupleBetaRow^[n.val]) r=s := by
  decide +kernel +revert

/-- The pair stabilizer connects all coordinate crosses in either of its two other-row classes. -/
theorem couple_coordinate_other_rows_transitive (r s : Fin 7) (hr : r≠0) (hs : s≠0)
    (hclass : (r=4 ∨ r=5) ↔ (s=4 ∨ s=5)) (x y : E) :
    ∃g : codeCoupleStabilizer,g.val • coordinateCross (rowLabel r,x)=coordinateCross (rowLabel s,y) := by
  obtain ⟨n,hn⟩ := coupleBeta_other_row_connected r s hr hs hclass
  let b : codeCoupleStabilizer := ⟨coupleCodeBeta^n.val,coupleBeta_pow_fix n.val⟩
  let z := (b.val.val.right (rowLabel r,x)).2
  have hb : b.val.val.right (rowLabel r,x)=(rowLabel s,z) := by
    apply Prod.ext
    · exact (coupleBeta_pow_row_coordinate n.val r x).trans (congrArg rowLabel hn)
    · rfl
  have hs0 : rowLabel s≠rowLabel 0 := fun h=>hs (rowLabel_bijective.1 h)
  obtain ⟨g,hg⟩ := couple_other_row_translation (rowLabel s) hs0 z y
  refine ⟨g*b,?_⟩
  change (g.val*b.val) • coordinateCross (rowLabel r,x)=_
  rw [mul_smul,coordinateCross_action,hb]
  exact hg



theorem coordinate_reference_row_four_cases (x : E) :
    coordinateCross (rowLabel 0,x)=localReferenceCross ∨
    coordinateCross (rowLabel 0,x)=referenceSecondCross ∨
    coordinateCross (rowLabel 0,x)=coordinateCross (originalCoordinateEquiv (0,4)) ∨
    coordinateCross (rowLabel 0,x)=coordinateCross (originalCoordinateEquiv (0,6)) := by
  have hc : ∀x : E,∃j : Fin 4,
      (rowLabel 0,x)=originalCoordinateEquiv (0,(![1,2,4,6] j)) ∨
      (rowLabel 0,x+(rowLabel 0).val)=originalCoordinateEquiv (0,(![1,2,4,6] j)) := by
    decide +kernel
  obtain ⟨j,hj⟩ := hc x
  have he : coordinateCross (rowLabel 0,x)=coordinateCross (originalCoordinateEquiv (0,(![1,2,4,6] j))) := by
    apply (coordinateCross_eq_iff _ _).mpr
    simpa only [codeI_coordinate] using hj
  fin_cases j
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (Or.inl he))
  · exact Or.inr (Or.inr (Or.inr he))

theorem coupleCodeR_swap_last_two :
    codeR • coordinateCross (originalCoordinateEquiv (0,4))=coordinateCross (originalCoordinateEquiv (0,6)) ∧
    codeR • coordinateCross (originalCoordinateEquiv (0,6))=coordinateCross (originalCoordinateEquiv (0,4)) := by
  constructor <;> rw [coordinateCross_action,codeR_right,original_congr_apply] <;> rfl

theorem couple_coordinate_reference_row_transitive (v w : MinimalCross)
    (hv : v∈coordinateRowFrame (rowLabel 0)) (hw : w∈coordinateRowFrame (rowLabel 0))
    (hvx : v≠localReferenceCross) (hvy : v≠referenceSecondCross)
    (hwx : w≠localReferenceCross) (hwy : w≠referenceSecondCross) :
    ∃g : codeCoupleStabilizer,g.val • v=w := by
  obtain ⟨x,rfl⟩ := hv
  obtain ⟨y,rfl⟩ := hw
  have hx := (coordinate_reference_row_four_cases x).resolve_left hvx |>.resolve_left hvy
  have hy := (coordinate_reference_row_four_cases y).resolve_left hwx |>.resolve_left hwy
  let R : codeCoupleStabilizer := ⟨codeR,coupleCodeR_fixes_reference⟩
  rcases hx with hx|hx <;> rcases hy with hy|hy
  · exact ⟨1,by simpa only [Subgroup.coe_one,one_smul] using hx.trans hy.symm⟩
  · exact ⟨R,by change codeR • coordinateCross (rowLabel 0,x)=coordinateCross (rowLabel 0,y); rw [hx,hy,coupleCodeR_swap_last_two.1]⟩
  · exact ⟨R,by change codeR • coordinateCross (rowLabel 0,x)=coordinateCross (rowLabel 0,y); rw [hx,hy,coupleCodeR_swap_last_two.2]⟩
  · exact ⟨1,by simpa only [Subgroup.coe_one,one_smul] using hx.trans hy.symm⟩

 theorem couple_coordinate_outside_dozen_transitive (v w : MinimalCross)
    (hv : v∈coordinateFrame\referenceCoordinateDozen)
    (hw : w∈coordinateFrame\referenceCoordinateDozen) :
    ∃g : codeCoupleStabilizer,g.val • v=w := by
  obtain ⟨⟨p,x⟩,rfl⟩ := coordinateFrame_rep v hv.1
  obtain ⟨⟨q,y⟩,rfl⟩ := coordinateFrame_rep w hw.1
  obtain ⟨r,rfl⟩ := rowLabel_bijective.2 p
  obtain ⟨s,rfl⟩ := rowLabel_bijective.2 q
  have hr : ¬(r=0 ∨ r=4 ∨ r=5) := by
    simpa only [referenceCoordinateDozen,coordinateCross_mem_selectedRows_iff,referenceDozenRows_marking] using hv.2
  have hs : ¬(s=0 ∨ s=4 ∨ s=5) := by
    simpa only [referenceCoordinateDozen,coordinateCross_mem_selectedRows_iff,referenceDozenRows_marking] using hw.2
  exact couple_coordinate_other_rows_transitive r s (fun h=>hr (Or.inl h))
    (fun h=>hs (Or.inl h)) (by tauto) x y

 theorem couple_coordinate_dozen_other_rows_transitive (v w : MinimalCross)
    (hv : v∈referenceCoordinateDozen\coordinateRowFrame (rowLabel 0))
    (hw : w∈referenceCoordinateDozen\coordinateRowFrame (rowLabel 0)) :
    ∃g : codeCoupleStabilizer,g.val • v=w := by
  obtain ⟨⟨p,x⟩,rfl⟩ := coordinateFrame_rep v (referenceCoordinateDozen_subset hv.1)
  obtain ⟨⟨q,y⟩,rfl⟩ := coordinateFrame_rep w (referenceCoordinateDozen_subset hw.1)
  obtain ⟨r,rfl⟩ := rowLabel_bijective.2 p
  obtain ⟨s,rfl⟩ := rowLabel_bijective.2 q
  have hr : r=0 ∨ r=4 ∨ r=5 := by
    simpa only [referenceCoordinateDozen,coordinateCross_mem_selectedRows_iff,referenceDozenRows_marking] using hv.1
  have hs : s=0 ∨ s=4 ∨ s=5 := by
    simpa only [referenceCoordinateDozen,coordinateCross_mem_selectedRows_iff,referenceDozenRows_marking] using hw.1
  have hr0 : r≠0 := by intro h; subst r; exact hv.2 ⟨x,rfl⟩
  have hs0 : s≠0 := by intro h; subst s; exact hw.2 ⟨y,rfl⟩
  exact couple_coordinate_other_rows_transitive r s hr0 hs0 (by tauto) x y

end Atlas.Rudvalis

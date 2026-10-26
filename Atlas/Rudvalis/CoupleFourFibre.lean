import Atlas.Rudvalis.FourLocalTransitivity
import Atlas.Rudvalis.CoupleMonomialGenerators

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

/-- Fixing one coordinate cross forces preservation of its coordinate row. -/
theorem code_fix_coordinate_row (g : codeGroup) (p : Point) (x : E)
    (hg : g • coordinateCross (p,x)=coordinateCross (p,x)) (y : E) :
    ∃z : E,g • coordinateCross (p,y)=coordinateCross (p,z) := by
  rw [coordinateCross_action] at hg ⊢
  have hp : (g.val.right (p,x)).1=p := by
    rcases (coordinateCross_eq_iff _ _).mp hg with h|h
    · exact congrArg Prod.fst h
    · rw [codeI_coordinate] at h
      exact congrArg Prod.fst h
  have hl := codeBlockLinear_coordinates g (p,x)
  have hy := codeBlockLinear_coordinates g (p,y)
  have he : (g.val.right (p,y)).1=p := Subtype.ext (hy.symm.trans (hl.trans (congrArg Subtype.val hp)))
  refine ⟨(g.val.right (p,y)).2,?_⟩
  congr 1
  exact Prod.ext he rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16384 in
theorem fourLocal_original_fix_row (k : Fin 8) :
    (fourLocalOriginalA.right (0,k)=(0,k) ∨
      fourLocalOriginalA.right (0,k)=((seedUnitMonomial 4).right (0,k))) ∧
    (fourLocalOriginalB.right (0,k)=(0,k) ∨
      fourLocalOriginalB.right (0,k)=((seedUnitMonomial 4).right (0,k))) := by
  decide +kernel +revert



theorem original_coordinate_cross_fix_at (g : codeGroup) (h : SignedCoordinates SeedCoordinate)
    (hg : g.val=seedConjugateHom h) (z : SeedCoordinate)
    (hh : h.right z=z ∨ h.right z=(seedUnitMonomial 4).right z) :
    g • coordinateCross (originalCoordinateEquiv z)=coordinateCross (originalCoordinateEquiv z) := by
  rw [coordinateCross_action,hg]
  change coordinateCross ((seedConjugateMonomial h).right (originalCoordinateEquiv z))=_
  rw [seedConjugateMonomial_right,original_congr_apply]
  rcases hh with hh|hh
  · rw [hh]
  · rw [hh]
    have hi : codeI.val.right (originalCoordinateEquiv z)=
        originalCoordinateEquiv ((seedUnitMonomial 4).right z) := by
      change (seedConjugateMonomial (seedUnitMonomial 4)).right (originalCoordinateEquiv z)=_
      rw [seedConjugateMonomial_right,original_congr_apply]
    rw [←hi,coordinateCross_I]

theorem fourLocalCode_fix_row (x : E) :
    fourLocalCodeA • coordinateCross (rowLabel 0,x)=coordinateCross (rowLabel 0,x) ∧
    fourLocalCodeB • coordinateCross (rowLabel 0,x)=coordinateCross (rowLabel 0,x) := by
  obtain ⟨k,hk⟩ := (seedInnerLabel_bijective 0).surjective x
  let j := signedPositionIndex k
  have hj : signedPositionIndex j=k := by
    dsimp [j]
    decide +kernel +revert
  have hz : originalCoordinateEquiv (0,j)=(rowLabel 0,x) := by
    change (rowLabel 0,seedInnerLabel 0 (signedPositionIndex j))=_
    rw [hj,hk]
  rw [←hz]
  exact ⟨original_coordinate_cross_fix_at _ _ fourLocalCodeA_transport _ (fourLocal_original_fix_row j).1,
    original_coordinate_cross_fix_at _ _ fourLocalCodeB_transport _ (fourLocal_original_fix_row j).2⟩

theorem fourLocalOrbitElement_fix_row (v : E) (b c : Bool) (x : E) :
    fourLocalOrbitElement v b c • coordinateCross (rowLabel 0,x)=coordinateCross (rowLabel 0,x) := by
  have hr : seedARowSign v • coordinateCross (rowLabel 0,x)=coordinateCross (rowLabel 0,x) := by
    rw [coordinateCross_action]
    rfl
  rw [fourLocalOrbitElement,mul_smul]
  have hs : fourLocalSignsCode b c • coordinateCross (rowLabel 0,x)=coordinateCross (rowLabel 0,x) := by
    cases b <;> cases c <;>
      simp only [fourLocalSignsCode,Bool.false_eq_true,ite_false,ite_true,
        mul_smul,one_smul,(fourLocalCode_fix_row x).1,(fourLocalCode_fix_row x).2]
  rw [hs,hr]



theorem monomial_reduce_congr (g : codeGroup) (v w : QuaternaryWord) (h : reduce v=reduce w) :
    reduce (monomialHom g.val v)=reduce (monomialHom g.val w) := by
  change reduce (monomialAction g.val v)=reduce (monomialAction g.val w)
  simp only [monomialAction_reduce,h]

/-- Every signed minimum fibre is transitive under elements fixing the reference row pointwise. -/
theorem fourCouple_same_residue_transitive (v w : QuaternaryWord)
    (hv : v∈quaternaryCode) (hw : w∈quaternaryCode)
    (hv16 : euclideanWeight v=16) (hw16 : euclideanWeight w=16)
    (hf : admissibleFourSupport (reduce v))
    (hz : ∀x : E,reduce v (rowLabel 0,x)=0) (he : reduce v=reduce w) :
    ∃t : codeGroup,(∀x : E,t • coordinateCross (rowLabel 0,x)=coordinateCross (rowLabel 0,x)) ∧
      monomialHom t.val v=w := by
  obtain ⟨g,hg⟩ := fourLocal_minimum_word_orbit v hv hv16 hf hz
  let u := monomialHom g.val.val⁻¹ w
  have hu : u∈quaternaryCode := (g.val⁻¹).prop w |>.mp hw
  have hu16 : euclideanWeight u=16 := (monomial_euclideanWeight _ _).trans hw16
  have hur : reduce u=fourPlaneSeedResidue := by
    have h := monomial_reduce_congr g.val⁻¹ w v he.symm
    change reduce u=reduce (monomialHom g.val.val⁻¹ v) at h
    rw [←hg] at h
    simpa using h.trans (by simpa using fourthSeed_residue)
  obtain ⟨⟨a,b,c⟩,habc⟩ := fourLocalOrbitLift_surjective ⟨⟨u,hu⟩,hu16,hur⟩
  let h := fourLocalOrbitElement a b c
  have hh : monomialHom h.val (quaternarySeed (3,0,0,0))=u :=
    congrArg (fun z : minimumLift fourPlaneSeedResidue => z.val.val) habc
  refine ⟨g.val*h*g.val⁻¹,?_,?_⟩
  · intro x
    have hgfix : g.val⁻¹ • coordinateCross (rowLabel 0,0)=coordinateCross (rowLabel 0,0) := by
      have hp := g⁻¹.prop
      change g.val⁻¹ • coordinateCross (originalCoordinateEquiv (0,1))=_ at hp
      rwa [(originalCoordinate_pair 0).1] at hp
    obtain ⟨z,hz⟩ := code_fix_coordinate_row g.val⁻¹ (rowLabel 0) 0 hgfix x
    rw [mul_smul,mul_smul,hz,fourLocalOrbitElement_fix_row,←hz,smul_inv_smul]
  · change monomialHom (g.val.val*h.val*g.val.val⁻¹) v=w
    rw [map_mul,map_mul]
    change monomialHom g.val.val (monomialHom h.val (monomialHom g.val.val⁻¹ v))=w
    rw [←hg]
    have hinv : monomialHom g.val.val⁻¹ (monomialHom g.val.val (quaternarySeed (3,0,0,0)))=
        quaternarySeed (3,0,0,0) := by simp
    rw [hinv]
    rw [hh]
    change monomialHom g.val.val (monomialHom g.val.val⁻¹ w)=w
    simp

end Atlas.Rudvalis

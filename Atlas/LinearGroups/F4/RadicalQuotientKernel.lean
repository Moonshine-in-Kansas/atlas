import Atlas.LinearGroups.F4.ParabolicOppositeDecomposition
import Atlas.LinearGroups.F4.ParabolicQuotientAction

/-! The explicit radical acts trivially on the actual seven-dimensional quotient.
Consequently the opposite-pair subgroup has the same quotient image as the full
point stabilizer. No order or normality assertion is used. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

theorem sevenCoordinates_eq_of_central_eq {x y : Carrier F}
    (h : centralSevenCoordinates x=centralSevenCoordinates y) :
    parabolicSevenCoordinates x=parabolicSevenCoordinates y := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  have h6 := congrFun h 6
  simp [centralSevenCoordinates] at h0 h1 h2 h3 h4 h5 h6
  apply Prod.ext
  · ext i; cases i with
    | inl i => fin_cases i <;> assumption
    | inr i => fin_cases i <;> assumption
  · exact h6

theorem radicalElement_seven (p : RadicalParameters F)
    (x : parabolicCrossTrace (F:=F)) :
    parabolicSevenCoordinates ((radicalElement p).val x.val)=parabolicSevenCoordinates x.val := by
  have hk := (parabolicCross_eq_zero_iff x.val).mp x.prop.1
  have hx : x.val.2 2 7=0 := hk.2.2.2.2.2.2.2.2.2
  have hl : oppositeLowerCoordinates x.val=0 := by
    ext i; fin_cases i <;> simp [oppositeLowerCoordinates,hk]
  have hc : centralSevenCoordinates ((halfWord p.point).val x.val)=centralSevenCoordinates x.val := by
    have h := halfWord_central_difference p.point x.val 0 hx
    simp only [map_zero] at h
    have hz : centralSevenCoordinates (0 : Carrier F)=0 := by
      ext i; fin_cases i <;> simp [centralSevenCoordinates]
    have hz' : oppositeLowerCoordinates (0 : Carrier F)=0 := by
      ext i; fin_cases i <;> rfl
    rw [hz,hz',hl,sub_zero,sub_self] at h
    have hb : halfWordBilinear p.point 0=0 := by
      rw [←halfWordBilinearMap_apply,map_zero]
    simpa only [hb,add_zero,sub_zero] using h
  apply sevenCoordinates_eq_of_central_eq
  change centralSevenCoordinates (centralSevenApply _ ((halfWord p.point).val x.val))=_
  rw [centralSeven_coordinates,(halfWord_lower p.point x.val).1,hx,zero_smul,add_zero,hc]

theorem radicalParabolic_orthogonal (p : RadicalParameters F) :
    parabolicOrthogonalHom (radicalParabolicHom p)=1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  obtain ⟨x,rfl⟩ := parabolicSevenMap_surjective v
  change parabolicSevenEquiv (radicalParabolicHom p) (parabolicSevenMap x)=parabolicSevenMap x
  rw [parabolicSevenEquiv_apply]
  exact radicalElement_seven p x

def pairOrthogonalHom : oppositePairStabilizer (F:=F) →* Atlas.Orthogonal.O_B 3 F :=
  parabolicOrthogonalHom.comp (oppositePairStabilizer (F:=F)).subtype

theorem pairOrthogonalHom_range_eq :
    (pairOrthogonalHom (F:=F)).range=parabolicOrthogonalHom.range := by
  apply le_antisymm
  · rintro _ ⟨l,rfl⟩
    exact ⟨l.val,rfl⟩
  · rintro _ ⟨g,rfl⟩
    obtain ⟨p,l,he⟩ := parabolic_factorization g
    refine ⟨l,?_⟩
    rw [he,map_mul,radicalParabolic_orthogonal,one_mul]
    rfl

end Atlas.F4

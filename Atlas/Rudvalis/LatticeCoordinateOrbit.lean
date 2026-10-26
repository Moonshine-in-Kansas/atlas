import Atlas.Rudvalis.LatticeShellCount
import Atlas.Rudvalis.LatticeMonomial

/-! The 112 signed coordinate minima form one orbit of the actual signed code group. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem binaryCoordinate_transitive (z w : Coordinate) :
    ∃ g : binaryPermutationGroup,g.val z=w := by
  have ho (p : Point) : ∃ q : Point,p≠q := by decide +kernel +revert
  obtain ⟨p,hp⟩ := ho z.1
  obtain ⟨q,hq⟩ := ho w.1
  obtain ⟨g,hg,_⟩ := binaryBlockHom_doubly_transitive z.1 p w.1 q hp hq
  have hrow : (g.val z).1=w.1 := (binaryBlockPermutation_coordinates g z).trans hg
  obtain ⟨i,hi⟩ := point_has_one w.1
  let u := (basisPoint i).val
  have hu : dot u w.1.val=1 := by rw [dot_basisPoint]; exact hi
  let B := outerMatrix (w.2+(g.val z).2) u
  refine ⟨⟨coordinateTranslation B,coordinateTranslation_mem B⟩*g,?_⟩
  change ((g.val z).1,(g.val z).2+matrixAt B (g.val z).1.val)=w
  apply Prod.ext
  · exact hrow
  · rw [hrow,matrixAt_outer,hu,one_smul]
    simp [add_left_comm,vector_add_self]

theorem codeCoordinate_transitive (z w : Coordinate) :
    ∃ g : codeGroup,g.val.right z=w := by
  obtain ⟨p,hp⟩ := binaryCoordinate_transitive z w
  obtain ⟨g,hg⟩ := codePermutationHom_surjective p
  refine ⟨g,?_⟩
  have he : g.val.right=p.val := congrArg Subtype.val hg
  rwa [he]

theorem rationalMonomial_coordinateMinimum (g : SignedCoordinates Coordinate) (i : Coordinate) :
    rationalMonomialHom g (coordinateMinimum i)=
      if g.left.toAdd (g.right i)=0 then coordinateMinimum (g.right i) else -coordinateMinimum (g.right i) := by
  classical
  funext j
  change liftedSign (g.left.toAdd j) (coordinateMinimum i (g.right.symm j))=_
  by_cases hj : j=g.right i
  · subst j
    by_cases hs : g.left.toAdd (g.right i)=0 <;> simp [coordinateMinimum,liftedSign,hs]
  · have hn : g.right.symm j≠i := by intro h; apply hj; exact g.right.symm_apply_eq.mp h
    by_cases hs : g.left.toAdd (g.right i)=0 <;> simp [coordinateMinimum,liftedSign,hj,hn,hs]

/-- Every code symmetry takes a positive coordinate minimum to one of the two signs. -/
theorem rationalMonomial_coordinate_sign (g : codeGroup) (i j : Coordinate) (hg : g.val.right i=j) :
    rationalMonomialHom g.val (coordinateMinimum i)=coordinateMinimum j ∨
      rationalMonomialHom g.val (coordinateMinimum i)= -coordinateMinimum j := by
  rw [rationalMonomial_coordinateMinimum,hg]
  split <;> simp

theorem coordinateMinimum_positive_orbit (i j : Coordinate) :
    ∃ g : codeGroup,rationalMonomialHom g.val (coordinateMinimum i)=coordinateMinimum j := by
  obtain ⟨g,hg⟩ := codeCoordinate_transitive i j
  rcases rationalMonomial_coordinate_sign g i j hg with h|h
  · exact ⟨g,h⟩
  · refine ⟨codeI*codeI*g,?_⟩
    change rationalMonomialHom ((codeI.val*codeI.val)*g.val) (coordinateMinimum i)=_
    rw [codeI_squared_signed,map_mul,LinearEquiv.mul_apply,h,negativeMonomial_rational,neg_neg]

theorem coordinateShell_transitive (a b : Coordinate × Bool) :
    ∃ g : codeGroup,rationalMonomialHom g.val (coordinateShellLift a).val.val=(coordinateShellLift b).val.val := by
  obtain ⟨g,hg⟩ := coordinateMinimum_positive_orbit a.1 b.1
  rcases a with ⟨i,a⟩
  rcases b with ⟨j,b⟩
  cases a <;> cases b
  · refine ⟨g,?_⟩
    change rationalMonomialHom g.val (-coordinateMinimum i)= -coordinateMinimum j
    rw [map_neg,hg]
  · refine ⟨codeI*codeI*g,?_⟩
    change rationalMonomialHom ((codeI.val*codeI.val)*g.val) (-coordinateMinimum i)=coordinateMinimum j
    rw [codeI_squared_signed,map_mul,LinearEquiv.mul_apply,map_neg,hg,negativeMonomial_rational,neg_neg]
  · refine ⟨codeI*codeI*g,?_⟩
    change rationalMonomialHom ((codeI.val*codeI.val)*g.val) (coordinateMinimum i)= -coordinateMinimum j
    rw [codeI_squared_signed,map_mul,LinearEquiv.mul_apply,hg,negativeMonomial_rational]
  · exact ⟨g,hg⟩


theorem coordinateShell_stable (g : codeGroup) (a : Coordinate × Bool) :
    ∃ b : Coordinate × Bool,rationalMonomialHom g.val (coordinateShellLift a).val.val=
      (coordinateShellLift b).val.val := by
  rcases a with ⟨i,a⟩
  rcases rationalMonomial_coordinate_sign g i (g.val.right i) rfl with h|h
  · cases a
    · refine ⟨(g.val.right i,false),?_⟩
      change rationalMonomialHom g.val (-coordinateMinimum i)= -coordinateMinimum (g.val.right i)
      rw [map_neg,h]
    · exact ⟨(g.val.right i,true),h⟩
  · cases a
    · refine ⟨(g.val.right i,true),?_⟩
      change rationalMonomialHom g.val (-coordinateMinimum i)=coordinateMinimum (g.val.right i)
      rw [map_neg,h,neg_neg]
    · exact ⟨(g.val.right i,false),h⟩

end Atlas.Rudvalis

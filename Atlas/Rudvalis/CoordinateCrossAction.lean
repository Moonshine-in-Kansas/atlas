import Atlas.Rudvalis.CoordinateCrossRows

namespace Atlas.Rudvalis

theorem coordinateCross_action (g : codeGroup) (i : Coordinate) :
    g • coordinateCross i=coordinateCross (g.val.right i) := by
  change minimalCross (g • coordinateShellLift (i,true))=_
  have hv := rationalMonomial_coordinateMinimum g.val i
  split_ifs at hv with h
  · have he : g • coordinateShellLift (i,true)=coordinateShellLift (g.val.right i,true) :=
      Subtype.ext (Subtype.ext hv)
    rw [he]
    rfl
  · have he : g • coordinateShellLift (i,true)=coordinateShellLift (g.val.right i,false) :=
      Subtype.ext (Subtype.ext hv)
    rw [he,coordinateCross_negative]

/-- Independent values can be assigned to a linear map at two distinct nonzero vectors. -/
theorem matrixAt_two_points (p q : Point) (hpq : p≠q) (a b : E) :
    ∃ B : BinaryMatrix,matrixAt B p.val=a ∧ matrixAt B q.val=b := by
  have sep : ∀p q : Point,p≠q → ∃u : E,dot u p.val=1 ∧ dot u q.val=0 := by
    decide +kernel
  obtain ⟨u,hup,huq⟩ := sep p q hpq
  obtain ⟨v,hvq,hvp⟩ := sep q p hpq.symm
  refine ⟨outerMatrix a u+outerMatrix b v,?_,?_⟩
  · funext i
    simp [matrixAt,outerMatrix,add_mul,mul_assoc,Finset.sum_add_distrib,←Finset.mul_sum,dot] at hup hvp ⊢
    rw [hup,hvp]
    simp
  · funext i
    simp [matrixAt,outerMatrix,add_mul,mul_assoc,Finset.sum_add_distrib,←Finset.mul_sum,dot] at huq hvq ⊢
    rw [huq,hvq]
    simp

theorem binaryCoordinate_two_rows (p q r : Point) (hpq : p≠q) (hpr : p≠r)
    (x y z : E) : ∃g : binaryPermutationGroup,g.val (p,x)=(p,x) ∧ g.val (q,y)=(r,z) := by
  obtain ⟨g,hp,hq⟩ := binaryBlockHom_doubly_transitive p q p r hpq hpr
  have hgp : (g.val (p,x)).1=p := (binaryBlockPermutation_coordinates g (p,x)).trans hp
  have hgq : (g.val (q,y)).1=r := (binaryBlockPermutation_coordinates g (q,y)).trans hq
  obtain ⟨B,hBp,hBr⟩ := matrixAt_two_points p r hpr (x+(g.val (p,x)).2) (z+(g.val (q,y)).2)
  refine ⟨⟨coordinateTranslation B,coordinateTranslation_mem B⟩*g,?_,?_⟩
  · change ((g.val (p,x)).1,(g.val (p,x)).2+matrixAt B (g.val (p,x)).1.val)=(p,x)
    rw [hgp,hBp]
    simp [add_left_comm,vector_add_self]
  · change ((g.val (q,y)).1,(g.val (q,y)).2+matrixAt B (g.val (q,y)).1.val)=(r,z)
    rw [hgq,hBr]
    simp [add_left_comm,vector_add_self]

theorem coordinateCross_other_rows_transitive (p q r : Point) (hpq : p≠q) (hpr : p≠r)
    (x y z : E) : ∃g : MulAction.stabilizer codeGroup (coordinateCross (p,x)),
      g.val • coordinateCross (q,y)=coordinateCross (r,z) := by
  obtain ⟨b,hb,hc⟩ := binaryCoordinate_two_rows p q r hpq hpr x y z
  obtain ⟨g,hg⟩ := codePermutationHom_surjective b
  have he : g.val.right=b.val := congrArg Subtype.val hg
  have hfix : g∈MulAction.stabilizer codeGroup (coordinateCross (p,x)) := by
    change g • coordinateCross (p,x)=coordinateCross (p,x)
    rw [coordinateCross_action,he,hb]
  refine ⟨⟨g,hfix⟩,?_⟩
  rw [coordinateCross_action,he,hc]

end Atlas.Rudvalis

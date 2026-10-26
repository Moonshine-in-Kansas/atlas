import Atlas.Rudvalis.CrossOrthogonality
import Atlas.Rudvalis.GaussianFrame

namespace Atlas.Rudvalis

noncomputable def coordinateCross (i : Coordinate) : MinimalCross :=
  minimalCross (coordinateShellLift (i,true))

theorem coordinateCross_negative (i : Coordinate) :
    minimalCross (coordinateShellLift (i,false))=coordinateCross i := by
  apply (minimalCross_eq_iff _ _).mpr
  refine ⟨⟨codeI^2,Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2⟩,?_⟩
  apply Subtype.ext; apply Subtype.ext
  change rationalMonomialHom (codeI.val^2) (coordinateMinimum i)= -coordinateMinimum i
  rw [map_pow,pow_two,LinearEquiv.mul_apply]
  exact rationalI_square _

theorem coordinateCross_I (i : Coordinate) :
    coordinateCross (codeI.val.right i)=coordinateCross i := by
  have hh : minimalCross (codeI • coordinateShellLift (i,true))=coordinateCross i := by
    apply (minimalCross_eq_iff _ _).mpr
    exact ⟨⟨codeI,Subgroup.mem_zpowers _⟩,rfl⟩
  have hv := rationalMonomial_coordinateMinimum codeI.val i
  split_ifs at hv with h
  · have he : codeI • coordinateShellLift (i,true)=coordinateShellLift (codeI.val.right i,true) :=
      Subtype.ext (Subtype.ext hv)
    rw [he] at hh
    exact hh
  · have he : codeI • coordinateShellLift (i,true)=coordinateShellLift (codeI.val.right i,false) :=
      Subtype.ext (Subtype.ext hv)
    rw [he,coordinateCross_negative] at hh
    exact hh

theorem rationalDot_coordinate_left (i : Coordinate) (v : RationalSpace) :
    rationalDot (coordinateMinimum i) v=2*v i := by
  classical
  simp [rationalDot,coordinateMinimum,Pi.single_apply]

theorem coordinate_hermitianOrthogonal (i : Coordinate) (v : RationalSpace) :
    HermitianOrthogonal (coordinateMinimum i) v ↔ v i=0 ∧ v (codeI.val.right i)=0 := by
  unfold HermitianOrthogonal
  have hi : rationalI (coordinateMinimum i)=
      if codeI.val.left.toAdd (codeI.val.right i)=0 then coordinateMinimum (codeI.val.right i)
      else -coordinateMinimum (codeI.val.right i) := rationalMonomial_coordinateMinimum _ _
  rw [hi]
  split_ifs <;> simp [rationalDot_coordinate_left,rationalDot_neg_left]

theorem coordinateCross_mem (i : Coordinate) : coordinateCross i∈coordinateFrame :=
  (minimalCross_mem_coordinateFrame _).mpr ⟨(i,true),rfl⟩

theorem coordinateFrame_rep (x : MinimalCross) (hx : x∈coordinateFrame) :
    ∃i,coordinateCross i=x := by
  induction x using Quotient.inductionOn with | h v =>
    obtain ⟨⟨i,b⟩,he⟩ := (minimalCross_mem_coordinateFrame v).mp hx
    subst v
    cases b
    · exact ⟨i,(coordinateCross_negative i).symm⟩
    · exact ⟨i,rfl⟩

theorem coordinateFrame_orthogonal_iff (x y : MinimalCross)
    (hx : x∈coordinateFrame) (hy : y∈coordinateFrame) :
    CrossOrthogonal x y ↔ x≠y := by
  constructor
  · intro h he
    subst y
    exact crossOrthogonal_irrefl x h
  · intro h
    obtain ⟨i,rfl⟩ := coordinateFrame_rep x hx
    obtain ⟨j,rfl⟩ := coordinateFrame_rep y hy
    have hij : i≠j := by intro he; subst j; exact h rfl
    have hiij : codeI.val.right i≠j := by
      intro he
      subst j
      exact h (coordinateCross_I i).symm
    apply (crossOrthogonal_mk _ _).mpr
    change HermitianOrthogonal (coordinateMinimum i) (coordinateMinimum j)
    rw [coordinate_hermitianOrthogonal]
    simp [coordinateMinimum,Ne.symm hij,Ne.symm hiij]

theorem coordinateFrame_orthogonal_card (x : coordinateFrame) :
    Nat.card {y : coordinateFrame // CrossOrthogonal x.val y.val}=27 := by
  classical
  let : Fintype coordinateFrame := Fintype.ofFinite _
  let e : {y : coordinateFrame // CrossOrthogonal x.val y.val} ≃
      {y : coordinateFrame // ¬y=x} :=
    Equiv.subtypeEquivRight (fun y => by
      rw [coordinateFrame_orthogonal_iff _ _ x.prop y.prop]
      exact not_congr (Subtype.ext_iff.symm.trans eq_comm))
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  have hc : Fintype.card coordinateFrame=28 := by
    simpa [Nat.card_eq_fintype_card] using coordinateFrame_card
  simp [hc]

theorem codeI_coordinate (z : Coordinate) : codeI.val.right z=(z.1,z.2+z.1.val) := by
  have h := congrArg (fun g : binaryPermutationGroup => g.val z) (nineCodeGenerator_projection 0)
  change codeI.val.right z=(z.1,z.2+matrixAt (nineTranslationMatrix 0) z.1.val) at h
  have hm : nineTranslationMatrix 0=1 := by decide +kernel
  rw [hm] at h
  have hi (p : E) : matrixAt (1 : BinaryMatrix) p=p := by
    exact Matrix.one_mulVec p
  simpa only [hi] using h

theorem coordinate_hermitianOrthogonal_pair (p : Point) (x : E) (v : RationalSpace) :
    HermitianOrthogonal (coordinateMinimum (p,x)) v ↔ v (p,x)=0 ∧ v (p,x+p.val)=0 := by
  rw [coordinate_hermitianOrthogonal,codeI_coordinate]

end Atlas.Rudvalis

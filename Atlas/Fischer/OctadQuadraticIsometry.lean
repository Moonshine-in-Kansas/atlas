import Atlas.Fischer.OctadQuadraticForms

namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra
open scoped BigOperators

theorem octadComplementary_restriction_weights (O : Octad) (c : golay) :
    hammingNorm (octadEvenRestriction O c).val+hammingNorm (octadExteriorWord O c)=hammingNorm c.val := by
  classical
  simp only [hammingNorm_eq_sum]
  change (∑ i : O.val, if c.val i.val=0 then 0 else 1)+
    (∑ v : BinaryFour, if c.val ((octadExteriorCoordinates O).symm v).val=0 then 0 else 1) = _
  rw [Equiv.sum_comp (octadExteriorCoordinates O).symm
    (fun i : OctadExterior O => if c.val i.val=0 then (0 : ℕ) else 1)]
  have h := Fintype.sum_subtype_add_sum_subtype (fun i : Omega => i ∈ O.val)
    (fun i => if c.val i=0 then (0 : ℕ) else 1)
  have hi : Subtype.fintype (fun i : Omega => i ∈ O.val)=Finset.Subtype.fintype O.val :=
    Subsingleton.elim _ _
  rw [hi] at h
  exact h

/-- Doubly even Golay weight equates the two actual half-weight invariants on
complementary coordinate sets. -/
theorem octadHalfWeight_compatible (O : Octad) (c : golay) :
    binaryHalfWeight (octadEvenRestriction O c).val=binaryHalfWeight (octadExteriorWord O c) := by
  have hw := octadComplementary_restriction_weights O c
  have hO := octadEvenCode_even O (octadEvenRestriction O c)
  have hX := binaryQuadraticCode_even (octadQuadraticRestriction O c)
  change 2 ∣ hammingNorm (octadExteriorWord O c) at hX
  obtain ⟨k,hk⟩ := golay_doublyEven c.val c.property
  have hn : hammingNorm (octadEvenRestriction O c).val/2+
      hammingNorm (octadExteriorWord O c)/2=2*k := by omega
  have h := congrArg (fun n : ℕ => (n : Bit)) hn
  simp only [Nat.cast_add,Nat.cast_mul] at h
  change binaryHalfWeight (octadEvenRestriction O c).val+binaryHalfWeight (octadExteriorWord O c)=
    (2 : Bit)*(k : Bit) at h
  rw [show (2 : Bit)=0 from rfl,zero_mul] at h
  exact (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq _)

/-- The quotient comparison is a genuine isometry of the specified quadratic
forms, induced by the same actual Golay restriction on both sides. -/
noncomputable def octadQuadraticIsometry (O : Octad) :
    (octadClassQuadratic O).IsometryEquiv binaryQuadraticClassForm where
  __ := octadEvenQuadraticClassesEquiv O
  map_app' x := by
    obtain ⟨c,rfl⟩ := octadEvenClassMap_surjective O x
    change binaryQuadraticClassForm (octadEvenQuadraticClassesEquiv O (octadEvenClassMap O c)) =
      octadClassQuadratic O (octadEvenClassMap O c)
    rw [octadEvenQuadraticClassesEquiv_apply]
    change binaryHalfWeight (octadExteriorWord O c)=binaryHalfWeight (octadEvenRestriction O c).val
    exact (octadHalfWeight_compatible O c).symm

end Atlas.Fischer

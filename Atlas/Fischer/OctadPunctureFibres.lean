import Atlas.Fischer.OctadQuadraticRanks

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

/-- The two lifts of a punctured word differ by the actual marked octad. -/
theorem octadExteriorWord_eq_iff (O : Octad) (c d : golay) :
    octadExteriorWord O c = octadExteriorWord O d ↔
      c = d ∨ c = d + octadWord O := by
  constructor
  · intro h
    have hz : octadExteriorWord O (c-d)=0 := by rw [map_sub,h,sub_self]
    rcases octadExteriorWord_kernel_cases O (c-d) hz with he | he
    · exact Or.inl (sub_eq_zero.mp he)
    · right
      have hh := (sub_eq_iff_eq_add).mp he
      simpa only [add_comm] using hh
  · rintro (rfl | rfl)
    · rfl
    · rw [map_add]
      have hz : octadExteriorWord O (octadWord O)=0 := by
        apply (octadExteriorWord_eq_zero_iff O _).mpr
        intro i hi
        simp only [octadWord_apply,ite_eq_right hi]
      rw [hz,add_zero]

/-- Inside and outside restrictions jointly recover the original Golay word. -/
theorem golay_eq_of_octad_restrictions (O : Octad) (c d : golay)
    (hi : octadEvenRestriction O c=octadEvenRestriction O d)
    (he : octadExteriorWord O c=octadExteriorWord O d) : c=d := by
  apply Subtype.ext
  funext i
  by_cases h : i ∈ O.val
  · exact congrFun (congrArg Subtype.val hi) ⟨i,h⟩
  · have hx := congrFun he (octadExteriorCoordinates O ⟨i,h⟩)
    simpa only [octadExteriorWord,LinearMap.coe_mk,AddHom.coe_mk,
      Equiv.symm_apply_apply] using hx

/-- Puncturing is injective on each literal octad-intersection fibre. -/
theorem octadExteriorWord_injective_on_restriction (O : Octad) (S : Finset Omega) :
    Function.Injective (fun D : {D : Octad // D.val ∩ O.val=S} =>
      octadExteriorWord O (octadWord D.val)) := by
  intro D E h
  have hi : octadEvenRestriction O (octadWord D.val)=
      octadEvenRestriction O (octadWord E.val) := by
    apply octadEvenRestriction_eq_of_support
    rw [octadWord_support,octadWord_support,D.property,E.property]
  have hc := golay_eq_of_octad_restrictions O _ _ hi h
  apply Subtype.ext
  apply Subtype.ext
  simpa only [octadWord_support] using congrArg (fun c : golay => support c.val) hc

/-- The punctured weight in a literal fibre is forced by the octad weight. -/
theorem octadExteriorWord_weight_in_restriction (O D : Octad) (S : Finset Omega)
    (h : D.val ∩ O.val=S) :
    hammingNorm (octadExteriorWord O (octadWord D)) + S.card = 8 := by
  have hw := octadComplementary_restriction_weights O (octadWord D)
  rw [octadEvenRestriction_weight,octadWord_support,octadWord_weight,h] at hw
  omega

end Atlas.Fischer

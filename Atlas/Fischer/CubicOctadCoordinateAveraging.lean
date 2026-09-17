import Atlas.Fischer.MathieuOctadTranslations
import Atlas.Fischer.CubicCompletionIntersections

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The full retained octad stabilizer carries any interior point to any other. -/
theorem cubicOctadInterior_transport (D : Octad) (i j : OctadInterior D) :
    ∃ g : MathieuOctadStabilizer D, g.val.val i.val = j.val := by
  by_cases hij : i = j
  · exact ⟨1,by simpa using congrArg Subtype.val hij⟩
  have hc : ({i,j} : Finset (OctadInterior D)).card < (Finset.univ : Finset (OctadInterior D)).card := by
    rw [Finset.card_univ,← Nat.card_eq_fintype_card,octadInterior_card]
    simp [hij]
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hkk : k ≠ i ∧ k ≠ j := by
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hk
  have hki := hkk.1
  have hkj := hkk.2
  let p : alternatingGroup (OctadInterior D) :=
    ⟨Equiv.swap i j * Equiv.swap j k,by
      rw [Equiv.Perm.mem_alternatingGroup,map_mul,Equiv.Perm.sign_swap hij,
        Equiv.Perm.sign_swap (Ne.symm hkj)]
      norm_num⟩
  obtain ⟨g,hg⟩ := mathieuOctadAlternating_surjective D p
  refine ⟨g,?_⟩
  have he := congrArg (fun z : alternatingGroup (OctadInterior D) => z.val i) hg
  change mathieuOctadInteriorPerm D g i = _ at he
  have hp : p.val i = j := by
    simp [p,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hij (Ne.symm hki)]
  exact congrArg Subtype.val (he.trans hp)

theorem cubicOctadExterior_transport (D : Octad) (i j : OctadExterior D) :
    ∃ g : MathieuOctadStabilizer D, g.val.val i.val = j.val := by
  obtain ⟨g,hg,_⟩ := mathieuOctadPointwise_regular D i j
  exact ⟨g.val,congrArg Subtype.val hg⟩

abbrev CubicOctadCoordinateInvariant (D : Octad) (f : Omega → Scalar) : Prop :=
  ∀ (g : MathieuOctadStabilizer D) i, f (g.val.val i) = f i

theorem cubicOctadInvariant_inside_average (D : Octad) (f : Omega → Scalar)
    (hf : CubicOctadCoordinateInvariant D f) (i : OctadInterior D) :
    (∑ j : OctadInterior D, f j.val) = 8 * f i.val := by
  have he (j : OctadInterior D) : f j.val = f i.val := by
    obtain ⟨g,hg⟩ := cubicOctadInterior_transport D i j
    simpa only [hg] using hf g i.val
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card,octadInterior_card]
  norm_num

theorem cubicOctadInvariant_outside_average (D : Octad) (f : Omega → Scalar)
    (hf : CubicOctadCoordinateInvariant D f) (i : OctadExterior D) :
    (∑ j : OctadExterior D, f j.val) = 16 * f i.val := by
  have he (j : OctadExterior D) : f j.val = f i.val := by
    obtain ⟨g,hg⟩ := cubicOctadExterior_transport D i j
    simpa only [hg] using hf g i.val
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card,octadExterior_card]
  norm_num

end Atlas.Fischer

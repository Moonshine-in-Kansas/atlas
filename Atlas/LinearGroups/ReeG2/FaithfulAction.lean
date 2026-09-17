import Atlas.LinearGroups.ReeG2.ExactStabilizer

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- Faithfulness of the actual generated matrix group on its projective point set. -/
theorem pointAction_faithful (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) :
    letI := pointAction m hcard
    FaithfulSMul (Model F m) (pointSet (F := F) m) := by
  letI := pointAction m hcard
  apply faithfulSMul_iff.mpr
  intro g hg
  have hf : ∀ p ∈ pointSet m, pointRight g.val⁻¹ p = p := by
    intro p hp
    exact congrArg Subtype.val (hg ⟨p,hp⟩)
  have hb : g.val⁻¹ ∈ borel m hcard :=
    (fixes_infinity_iff_mem_borel m hcard _ ((generated F m).inv_mem g.property)).mp
      (hf infinityPoint ⟨none,rfl⟩)
  have he := congrArg Subtype.val (borel_action_faithful m hcard ⟨g.val⁻¹,hb⟩ hf)
  apply Subtype.ext
  change g.val = 1
  exact inv_eq_one.mp he

end Atlas.ReeG2

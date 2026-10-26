import Atlas.Comparisons.Exceptional.E6.RootWords
import Atlas.LinearGroups.Orthogonal.ReflectionConjugation
import Atlas.LinearGroups.Orthogonal.ReflectionGroup

/-! Every binary quadratic reflection is in the actual integral Weyl image.
Root reachability supplies the conjugating word; no group enumeration is used. -/
noncomputable section
namespace Atlas.Comparisons.E6Lattice
open Atlas.Orthogonal Atlas.Quadratic

abbrev binaryFirstRoot : Fin 6 → ZMod 2 := reduceBinary (simpleRoot 0)

theorem binaryFirstRoot_norm : form (ZMod 2) binaryFirstRoot = 1 := by decide

theorem intoBinaryOrthogonal_action (g : IntegralWeyl) (x : Fin 6 → ℤ) :
    (intoBinaryOrthogonal g).val (reduceBinary x) = reduceBinary (g.val.val x) :=
  binaryMatrix_action g x

theorem binary_weyl_reaches (v : Fin 6 → ZMod 2) (hv : norm v = 1) :
    ∃ g : IntegralWeyl, (intoBinaryOrthogonal g).val binaryFirstRoot = v := by
  obtain ⟨i,hi⟩ := binary_root_lift v hv
  obtain ⟨g,hg⟩ := weyl_reaches_every_root _ (rootRepresentative_norm i)
  exact ⟨g, (intoBinaryOrthogonal_action g (simpleRoot 0)).trans (by rw [hg,hi])⟩

theorem binary_simple_reflection :
    intoBinaryOrthogonal ⟨simpleReflection ℤ 0,simpleReflection_mem ℤ 0⟩ =
      reflectionElement (form (ZMod 2)) binaryFirstRoot (by rw [binaryFirstRoot_norm]; decide) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have ha := intoBinaryOrthogonal_action
    ⟨simpleReflection ℤ 0,simpleReflection_mem ℤ 0⟩ (binaryLift x)
  rw [reduceBinary_lift] at ha
  rw [ha]
  change reduceBinary (reflection 0 (binaryLift x)) =
    reflectionLinear (form (ZMod 2)) binaryFirstRoot (by rw [binaryFirstRoot_norm]; decide) x
  rw [reflectionLinear_apply, binaryFirstRoot_norm]
  simp only [inv_one, one_mul, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    form_apply]
  have hformula : ∀ x : Fin 6 → ZMod 2,
      reduceBinary (reflection 0 (binaryLift x)) =
      x - (norm (x + binaryFirstRoot) - norm x - norm binaryFirstRoot) • binaryFirstRoot := by
    decide
  exact hformula x

theorem binary_reflection_mem_range (v : Fin 6 → ZMod 2)
    (hv : form (ZMod 2) v ≠ 0) :
    reflectionElement (form (ZMod 2)) v hv ∈ intoBinaryOrthogonal.range := by
  have hv1 : norm v = 1 := by
    have h : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    exact h _ (by simpa only [form_apply] using hv)
  obtain ⟨g,hg⟩ := binary_weyl_reaches v hv1
  have hs : reflectionElement (form (ZMod 2)) binaryFirstRoot
      (by rw [binaryFirstRoot_norm]; decide) ∈ intoBinaryOrthogonal.range := by
    exact ⟨⟨simpleReflection ℤ 0,simpleReflection_mem ℤ 0⟩,binary_simple_reflection⟩
  have hm := intoBinaryOrthogonal.range.mul_mem
    (intoBinaryOrthogonal.range.mul_mem (show intoBinaryOrthogonal g ∈ intoBinaryOrthogonal.range from ⟨g,rfl⟩) hs)
    (intoBinaryOrthogonal.range.inv_mem (show intoBinaryOrthogonal g ∈ intoBinaryOrthogonal.range from ⟨g,rfl⟩))
  rw [reflectionElement_conj] at hm
  simpa only [hg] using hm

theorem binary_reflectionSubgroup_le_range :
    reflectionSubgroup (form (ZMod 2)) ≤ intoBinaryOrthogonal.range := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨v,hv,rfl⟩
  exact binary_reflection_mem_range v hv

end Atlas.Comparisons.E6Lattice

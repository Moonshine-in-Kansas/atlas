import Atlas.LinearGroups.Chevalley.RootData.DominantRootFunctional

/-! A secondary functional fixes signs inside the zero subsystem of a
dominant primary functional. Both functions are on actual root labels. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- An actual Weyl translate makes an odd primary function nonnegative on
simple roots, and an odd secondary function nonnegative on the simple roots
where the primary vanishes. This does not assume a root-pair chamber theorem. -/
theorem exists_rootWeyl_lex_dominant_functionals (f g : ι → ℚ)
    (hf : ∀ β, f (P.reflectionPerm β β) = -f β)
    (hg : ∀ β, g (P.reflectionPerm β β) = -g β) :
    ∃ w : P.weylGroupToPerm.range, ∀ i : b.support,
      0 ≤ f (w.val i.val) ∧
        (f (w.val i.val) = 0 → 0 ≤ g (w.val i.val)) := by
  obtain ⟨v, hv, hvmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset P.weylGroupToPerm.range)
    (rootFunctionalScore P b f) ⟨1, Finset.mem_univ _⟩
  let s := Finset.univ.filter fun w : P.weylGroupToPerm.range =>
    rootFunctionalScore P b f w = rootFunctionalScore P b f v
  have hvs : v ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  obtain ⟨w, hw, hwmax⟩ := Finset.exists_max_image s
    (rootFunctionalScore P b g) ⟨v, hvs⟩
  have hwf : rootFunctionalScore P b f w = rootFunctionalScore P b f v :=
    (Finset.mem_filter.mp hw).2
  refine ⟨w, fun i => ⟨?_, ?_⟩⟩
  · have hle := hvmax (w * simpleWeylReflection P b i) (Finset.mem_univ _)
    rw [rootFunctionalScore_mul_simple P b f hf, hwf] at hle
    linarith
  · intro hzero
    have hws : w * simpleWeylReflection P b i ∈ s := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [rootFunctionalScore_mul_simple P b f hf, hzero, mul_zero, sub_zero, hwf]
    have hle := hwmax (w * simpleWeylReflection P b i) hws
    rw [rootFunctionalScore_mul_simple P b g hg] at hle
    linarith

end Atlas.Chevalley.RootData

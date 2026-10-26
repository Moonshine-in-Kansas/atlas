import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionLength
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-! A dominant translate of an odd rational-valued function on root labels.
The maximum is taken over the finite actual root-permutation Weyl image.
No chamber theorem, Coxeter presentation or linear-group assertion is used. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

include b

/-- Every actual Weyl permutation preserves the opposite-root operation. -/
theorem rootWeyl_apply_opposite (w : P.weylGroupToPerm.range) (β : ι) :
    w.val (P.reflectionPerm β β) =
      P.reflectionPerm (w.val β) (w.val β) := by
  obtain ⟨l, hl⟩ := exists_simpleReflectionWord_of_mem P b w.property
  have hc := simpleReflectionWord_conjugate P b l β
  rw [hl] at hc
  rw [hc]
  simp

/-- The sum of a root-label function on the image of the positive roots. -/
def rootFunctionalScore (f : ι → ℚ) (w : P.weylGroupToPerm.range) : ℚ :=
  ∑ β ∈ Finset.univ.filter b.IsPos, f (w.val β)

private theorem positiveErase_reflection_mem (i : b.support) (β : ι)
    (hβ : β ∈ (Finset.univ.filter b.IsPos).erase i.val) :
    P.reflectionPerm i.val β ∈ (Finset.univ.filter b.IsPos).erase i.val := by
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hβ
  have hpos : b.IsPos β := (Finset.mem_filter.mp hmem).2
  have hnot : P.reflectionPerm i.val β ≠ i.val := by
    intro he
    have hroot : β = P.reflectionPerm i.val i.val := by
      calc
        β = P.reflectionPerm i.val (P.reflectionPerm i.val β) :=
          (P.reflectionPerm_self i.val β).symm
        _ = P.reflectionPerm i.val i.val := congrArg (P.reflectionPerm i.val) he
    exact not_isPos_reflection_simple P b i (hroot ▸ hpos)
  exact Finset.mem_erase.mpr ⟨hnot,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos.reflectionPerm i.property hne⟩⟩

/-- Crossing one simple wall changes the score by minus twice the value
at the corresponding image simple root. Only oddness of the function is used. -/
theorem rootFunctionalScore_mul_simple (f : ι → ℚ)
    (hodd : ∀ β, f (P.reflectionPerm β β) = -f β)
    (w : P.weylGroupToPerm.range) (i : b.support) :
    rootFunctionalScore P b f (w * simpleWeylReflection P b i) =
      rootFunctionalScore P b f w - 2 * f (w.val i.val) := by
  let s : Finset ι := Finset.univ.filter b.IsPos
  have hi : i.val ∈ s :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.isPos_of_mem_support i.property⟩
  have hs : (∑ β ∈ s.erase i.val, f (w.val (P.reflectionPerm i.val β))) =
      ∑ β ∈ s.erase i.val, f (w.val β) := by
    refine Finset.sum_nbij' (P.reflectionPerm i.val) (P.reflectionPerm i.val)
      ?_ ?_ ?_ ?_ ?_
    · intro β hβ
      exact positiveErase_reflection_mem P b i β hβ
    · intro β hβ
      exact positiveErase_reflection_mem P b i β hβ
    · intro β hβ
      exact P.reflectionPerm_self i.val β
    · intro β hβ
      exact P.reflectionPerm_self i.val β
    · intro β hβ
      rfl
  have h0 : f (w.val i.val) + (∑ β ∈ s.erase i.val, f (w.val β)) =
      rootFunctionalScore P b f w :=
    Finset.add_sum_erase s (fun β => f (w.val β)) hi
  have h1 : f (w.val (P.reflectionPerm i.val i.val)) +
      (∑ β ∈ s.erase i.val, f (w.val (P.reflectionPerm i.val β))) =
      rootFunctionalScore P b f (w * simpleWeylReflection P b i) :=
    Finset.add_sum_erase s (fun β => f (w.val (P.reflectionPerm i.val β))) hi
  rw [rootWeyl_apply_opposite P b w i.val, hodd, hs] at h1
  linarith

/-- Every odd rational-valued root-label function has an actual Weyl translate
which is nonnegative on every simple root. -/
theorem exists_rootWeyl_dominant_functional (f : ι → ℚ)
    (hodd : ∀ β, f (P.reflectionPerm β β) = -f β) :
    ∃ w : P.weylGroupToPerm.range, ∀ i : b.support, 0 ≤ f (w.val i.val) := by
  obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset P.weylGroupToPerm.range)
    (rootFunctionalScore P b f) ⟨1, Finset.mem_univ _⟩
  refine ⟨w, fun i => ?_⟩
  have hle := hmax (w * simpleWeylReflection P b i) (Finset.mem_univ _)
  rw [rootFunctionalScore_mul_simple P b f hodd] at hle
  linarith

/-- In particular, a rational-valued additive functional on the actual root
module has an actual Weyl translate nonnegative on all simple roots. -/
theorem exists_rootWeyl_dominant_addHom (f : M →+ ℚ) :
    ∃ w : P.weylGroupToPerm.range,
      ∀ i : b.support, 0 ≤ f (P.root (w.val i.val)) := by
  apply exists_rootWeyl_dominant_functional P b (fun β => f (P.root β))
  intro β
  rw [P.root_reflectionPerm, P.reflection_apply_self, map_neg]

end Atlas.Chevalley.RootData

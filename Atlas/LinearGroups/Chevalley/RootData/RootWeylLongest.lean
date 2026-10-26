import Atlas.LinearGroups.Chevalley.RootData.RootInversionLength
import Atlas.LinearGroups.Chevalley.RootData.RootHeightCombination
import Mathlib.Data.Finset.Max

/-! Longest element of the actual finite root-permutation Weyl group.
No abstract Coxeter presentation or linear-group assertion is used. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Negativity on all simple roots implies negativity on every positive root. -/
theorem rootWeyl_negative_of_simple_negative (w : P.weylGroupToPerm.range)
    (hsimple : ∀ i : b.support, ¬ b.IsPos (w.val i.val))
    {β : ι} (hβ : b.IsPos β) : ¬ b.IsPos (w.val β) := by
  obtain ⟨l, hl⟩ := exists_simpleReflectionWord_of_mem P b w.property
  have hn : ¬ b.IsPos (simpleReflectionWord P b l β) := by
    apply hβ.induction_on_add
    · intro i hi
      simpa only [hl] using hsimple ⟨i, hi⟩
    · intro i j k hk hi hj
      exact simpleReflectionWord_not_isPos_of_combination P b l i j k 1 1
        (by simpa only [one_smul] using hk) (by decide) (by decide) (by decide)
        hi (by simpa only [hl] using hsimple ⟨j, hj⟩)
  simpa only [hl] using hn

theorem exists_rootWeyl_maximal :
    ∃ w : P.weylGroupToPerm.range,
      ∀ v : P.weylGroupToPerm.range, rootWeylLength P b v ≤ rootWeylLength P b w := by
  obtain ⟨w, _, hw⟩ := Finset.exists_max_image
    (Finset.univ : Finset P.weylGroupToPerm.range) (rootWeylLength P b)
    (Finset.univ_nonempty)
  exact ⟨w, fun v => hw v (Finset.mem_univ v)⟩

/-- A longest element chosen inside the actual finite permutation subgroup. -/
def rootWeylLongest : P.weylGroupToPerm.range :=
  Classical.choose (exists_rootWeyl_maximal P b)

theorem rootWeylLongest_maximal (v : P.weylGroupToPerm.range) :
    rootWeylLength P b v ≤ rootWeylLength P b (rootWeylLongest P b) :=
  Classical.choose_spec (exists_rootWeyl_maximal P b) v

theorem rootWeyl_negative_of_maximal (w : P.weylGroupToPerm.range)
    (hmax : ∀ v : P.weylGroupToPerm.range,
      rootWeylLength P b v ≤ rootWeylLength P b w)
    {β : ι} (hβ : b.IsPos β) : ¬ b.IsPos (w.val β) := by
  apply rootWeyl_negative_of_simple_negative P b w _ hβ
  intro i hi
  have hle := hmax (w * simpleWeylReflection P b i)
  have hstep := rootWeylLength_mul_simple_of_positive P b w i hi
  omega

theorem rootWeylLongest_not_isPos {β : ι} (hβ : b.IsPos β) :
    ¬ b.IsPos ((rootWeylLongest P b).val β) :=
  rootWeyl_negative_of_maximal P b _ (rootWeylLongest_maximal P b) hβ

theorem rootInversions_longest :
    rootInversions P b (rootWeylLongest P b) =
      Finset.univ.filter (fun β : ι => b.IsPos β) := by
  ext β
  simp only [mem_rootInversions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.1, fun h => ⟨h, rootWeylLongest_not_isPos P b h⟩⟩

theorem rootWeylLength_longest :
    rootWeylLength P b (rootWeylLongest P b) =
      (Finset.univ.filter (fun β : ι => b.IsPos β)).card := by
  rw [← rootInversionCount_eq_rootWeylLength, rootInversionCount, rootInversions_longest]

private theorem rootWeyl_neg_sign (w : P.weylGroupToPerm.range) (β : ι) :
    b.IsPos (w.val (P.reflectionPerm β β)) ↔ ¬ b.IsPos (w.val β) := by
  obtain ⟨l, hl⟩ := exists_simpleReflectionWord_of_mem P b w.property
  have hc := simpleReflectionWord_conjugate P b l β
  rw [hl] at hc
  have he : w.val (P.reflectionPerm β β) =
      P.reflectionPerm (w.val β) (w.val β) := by
    rw [hc]
    simp
  rw [he]
  exact RootPairing.Base.IsPos.neg_iff_not b (w.val β)

theorem rootWeyl_sign_flip_of_negative (w : P.weylGroupToPerm.range)
    (hnegative : ∀ β : ι, b.IsPos β → ¬ b.IsPos (w.val β)) (β : ι) :
    b.IsPos (w.val β) ↔ ¬ b.IsPos β := by
  constructor
  · intro himage hβ
    exact hnegative β hβ himage
  · intro hβ
    have hnβ : b.IsPos (P.reflectionPerm β β) :=
      (RootPairing.Base.IsPos.neg_iff_not b β).mpr hβ
    have hn := hnegative (P.reflectionPerm β β) hnβ
    by_contra himage
    exact hn ((rootWeyl_neg_sign P b w β).mpr himage)

theorem rootWeylLongest_isPos_iff (β : ι) :
    b.IsPos ((rootWeylLongest P b).val β) ↔ ¬ b.IsPos β :=
  rootWeyl_sign_flip_of_negative P b _
    (fun _ hβ => rootWeylLongest_not_isPos P b hβ) β

theorem rootWeylLongest_mul_self :
    rootWeylLongest P b * rootWeylLongest P b = 1 := by
  apply (rootWeyl_preserves_positive_iff_one P b _).mp
  intro β hβ
  change b.IsPos ((rootWeylLongest P b).val ((rootWeylLongest P b).val β))
  exact (rootWeylLongest_isPos_iff P b _).mpr (rootWeylLongest_not_isPos P b hβ)

theorem rootWeylLongest_inv : (rootWeylLongest P b)⁻¹ = rootWeylLongest P b := by
  calc
    (rootWeylLongest P b)⁻¹ =
        (rootWeylLongest P b)⁻¹ * (rootWeylLongest P b * rootWeylLongest P b) := by
      rw [rootWeylLongest_mul_self, mul_one]
    _ = rootWeylLongest P b := by rw [← mul_assoc, inv_mul_cancel, one_mul]

theorem rootWeyl_eq_longest_of_negative (w : P.weylGroupToPerm.range)
    (hnegative : ∀ β : ι, b.IsPos β → ¬ b.IsPos (w.val β)) :
    w = rootWeylLongest P b := by
  have hprod : w * rootWeylLongest P b = 1 := by
    apply (rootWeyl_preserves_positive_iff_one P b _).mp
    intro β hβ
    change b.IsPos (w.val ((rootWeylLongest P b).val β))
    exact (rootWeyl_sign_flip_of_negative P b w hnegative _).mpr
      (rootWeylLongest_not_isPos P b hβ)
  calc
    w = (w * rootWeylLongest P b) * rootWeylLongest P b := by
      rw [mul_assoc, rootWeylLongest_mul_self, mul_one]
    _ = rootWeylLongest P b := by rw [hprod, one_mul]

end Atlas.Chevalley.RootData

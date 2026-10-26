import Atlas.LinearGroups.Chevalley.RootData.ReducedRootLabels
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop

/-! The ordered root labels of an actual simple-reflection word. For a reduced
word every label is positive and the labels are pairwise distinct. This is a
root-permutation result only, not independence of root subgroups. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Successive simple roots transported by their preceding word prefixes. -/
def rootWordLabels : List b.support → List ι
  | [] => []
  | i :: l => i.val :: (rootWordLabels l).map (P.reflectionPerm i.val)

@[simp] theorem rootWordLabels_length (l : List b.support) :
    (rootWordLabels P b l).length = l.length := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [rootWordLabels, List.length_cons, List.length_map, ih]

/-- A label occurrence has a literal prefix/letter/suffix decomposition. -/
theorem rootWordLabels_mem_decomposition (l : List b.support) {β : ι}
    (hβ : β ∈ rootWordLabels P b l) :
    ∃ (p : List b.support) (i : b.support) (r : List b.support),
      l = p ++ i :: r ∧ β = (rootWeylWord P b p).val i.val := by
  induction l generalizing β with
  | nil => exact False.elim (List.not_mem_nil hβ)
  | cons i l ih =>
    rcases List.mem_cons.mp hβ with heq | htail
    · subst β
      exact ⟨[], i, l, rfl, rfl⟩
    · obtain ⟨γ, hγ, hγβ⟩ := List.mem_map.mp htail
      obtain ⟨p, j, r, hl, hlabel⟩ := ih hγ
      refine ⟨i :: p, j, r, ?_, ?_⟩
      · simpa only [List.cons_append] using congrArg (List.cons i) hl
      · change β = P.reflectionPerm i.val ((rootWeylWord P b p).val j.val)
        rw [← hlabel]
        exact hγβ.symm

theorem rootWordLabels_getElem (l : List b.support) (n : ℕ) (hn : n < l.length) :
    (rootWordLabels P b l)[n]'(by simpa only [rootWordLabels_length] using hn) =
      (rootWeylWord P b (l.take n)).val (l[n].val) := by
  induction l generalizing n with
  | nil => simp only [List.length_nil] at hn; omega
  | cons i l ih =>
    cases n with
    | zero => rfl
    | succ n =>
      have hn' : n < l.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hn
      simp only [rootWordLabels, List.getElem_cons_succ, List.getElem_map,
        List.take_succ_cons]
      have hnlabels : n < (rootWordLabels P b l).length := by
        simpa only [rootWordLabels_length] using hn'
      change P.reflectionPerm i.val ((rootWordLabels P b l)[n]'hnlabels) =
        P.reflectionPerm i.val ((rootWeylWord P b (l.take n)).val (l[n].val))
      exact congrArg (P.reflectionPerm i.val) (ih n hn')

theorem isReducedRootWord_labels_positive (l : List b.support)
    (hred : IsReducedRootWord P b l) {β : ι} (hβ : β ∈ rootWordLabels P b l) :
    b.IsPos β := by
  obtain ⟨p, i, r, hl, hlabel⟩ := rootWordLabels_mem_decomposition P b l hβ
  rw [hlabel]
  apply isReducedRootWord_prefix_label_pos P b p r i
  simpa only [hl] using hred

theorem isReducedRootWord_labels_nodup (l : List b.support)
    (hred : IsReducedRootWord P b l) : (rootWordLabels P b l).Nodup := by
  revert hred
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons i l ih =>
    intro hred
    have htail : IsReducedRootWord P b l :=
      (isReducedRootWord_append_parts P b [i] l (by simpa only [List.singleton_append] using hred)).2
    simp only [rootWordLabels, List.nodup_cons]
    constructor
    · intro hmem
      obtain ⟨β, hβ, hβi⟩ := List.mem_map.mp hmem
      obtain ⟨p, j, r, hl, hlabel⟩ := rootWordLabels_mem_decomposition P b l hβ
      have hne := isReducedRootWord_prefix_labels_ne P b [] p r i j
        (by simpa only [List.nil_append, hl] using hred)
      apply hne
      change i.val = P.reflectionPerm i.val ((rootWeylWord P b p).val j.val)
      rw [← hlabel]
      exact hβi.symm
    · exact List.Nodup.map (P.reflectionPerm i.val).injective (ih htail)

/-- The root label at an actual word position, indexed by the word's length. -/
def rootWordLabelAt (l : List b.support) (k : Fin l.length) : ι :=
  (rootWordLabels P b l).get ⟨k.val, by simpa only [rootWordLabels_length] using k.isLt⟩

theorem rootWordLabelAt_eq_prefix (l : List b.support) (k : Fin l.length) :
    rootWordLabelAt P b l k = (rootWeylWord P b (l.take k.val)).val (l.get k).val :=
  rootWordLabels_getElem P b l k.val k.isLt

theorem isReducedRootWord_labelAt_positive (l : List b.support)
    (hred : IsReducedRootWord P b l) (k : Fin l.length) :
    b.IsPos (rootWordLabelAt P b l k) :=
  isReducedRootWord_labels_positive P b l hred (List.get_mem _ _)

theorem isReducedRootWord_labelAt_injective (l : List b.support)
    (hred : IsReducedRootWord P b l) : Function.Injective (rootWordLabelAt P b l) := by
  intro i j hij
  have heq := (isReducedRootWord_labels_nodup P b l hred).injective_get hij
  have hval : i.val = j.val :=
    congrArg (fun k : Fin (rootWordLabels P b l).length => k.val) heq
  exact Fin.ext hval

end Atlas.Chevalley.RootData

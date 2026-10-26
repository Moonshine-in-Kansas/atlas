import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionLength
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Induction

/-! Positive roots made negative by an actual root-permutation Weyl element.
Their number is the minimum actual simple-reflection word length. No Coxeter
presentation or constructed linear group is used. Source candidate only. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- The actual positive root labels carried to negative root labels. -/
def rootInversions (w : P.weylGroupToPerm.range) : Finset ι := by
  classical
  exact Finset.univ.filter (fun β => b.IsPos β ∧ ¬ b.IsPos (w.val β))

def rootInversionCount (w : P.weylGroupToPerm.range) : ℕ :=
  (rootInversions P b w).card

@[simp] theorem mem_rootInversions (w : P.weylGroupToPerm.range) (β : ι) :
    β ∈ rootInversions P b w ↔ b.IsPos β ∧ ¬ b.IsPos (w.val β) := by
  classical
  simp only [rootInversions, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem rootInversionCount_one :
    rootInversionCount P b 1 = 0 := by
  classical
  simp [rootInversionCount, rootInversions]

private theorem positive_reflection_ne_simple (i : b.support) {β : ι}
    (hβ : b.IsPos β) : P.reflectionPerm i.val β ≠ i.val := by
  intro h
  have hroot : β = P.reflectionPerm i.val i.val := by
    calc
      β = P.reflectionPerm i.val (P.reflectionPerm i.val β) :=
        (P.reflectionPerm_self i.val β).symm
      _ = P.reflectionPerm i.val i.val := congrArg (P.reflectionPerm i.val) h
  exact not_isPos_reflection_simple P b i (hroot ▸ hβ)

/-- Away from the crossed simple root, its reflection bijects the two
inversion sets. The exceptional simple root is erased on both sides. -/
theorem rootInversions_mul_simple_erase_card (w : P.weylGroupToPerm.range)
    (i : b.support) :
    ((rootInversions P b (w * simpleWeylReflection P b i)).erase i.val).card =
      ((rootInversions P b w).erase i.val).card := by
  apply Finset.card_equiv (P.reflectionPerm i.val)
  intro β
  simp only [Finset.mem_erase, mem_rootInversions]
  constructor
  · rintro ⟨hne, hpos, hneg⟩
    refine ⟨positive_reflection_ne_simple P b i hpos,
      hpos.reflectionPerm i.property hne, ?_⟩
    change ¬ b.IsPos (w.val (P.reflectionPerm i.val β)) at hneg
    exact hneg
  · rintro ⟨hne, hpos, hneg⟩
    have hβpos : b.IsPos β := by
      simpa only [P.reflectionPerm_self] using hpos.reflectionPerm i.property hne
    have hβne : β ≠ i.val := by
      intro heq
      exact not_isPos_reflection_simple P b i (heq ▸ hpos)
    refine ⟨hβne, hβpos, ?_⟩
    change ¬ b.IsPos (w.val (P.reflectionPerm i.val β))
    exact hneg

theorem rootInversionCount_mul_simple_of_positive (w : P.weylGroupToPerm.range)
    (i : b.support) (hpos : b.IsPos (w.val i.val)) :
    rootInversionCount P b (w * simpleWeylReflection P b i) =
      rootInversionCount P b w + 1 := by
  have hnot : i.val ∉ rootInversions P b w := by
    simp only [mem_rootInversions, not_and]
    intro _ hneg
    exact hneg hpos
  have hmem : i.val ∈ rootInversions P b (w * simpleWeylReflection P b i) := by
    rw [mem_rootInversions]
    refine ⟨b.isPos_of_mem_support i.property, ?_⟩
    intro h
    exact ((simpleWeylReflection_sign_flip P b w i).mp h) hpos
  calc
    rootInversionCount P b (w * simpleWeylReflection P b i) =
        ((rootInversions P b (w * simpleWeylReflection P b i)).erase i.val).card + 1 :=
      (Finset.card_erase_add_one hmem).symm
    _ = ((rootInversions P b w).erase i.val).card + 1 := by
      rw [rootInversions_mul_simple_erase_card]
    _ = rootInversionCount P b w + 1 := by
      rw [Finset.erase_eq_of_notMem hnot]
      rfl

theorem rootInversionCount_mul_simple_of_negative (w : P.weylGroupToPerm.range)
    (i : b.support) (hneg : ¬ b.IsPos (w.val i.val)) :
    rootInversionCount P b (w * simpleWeylReflection P b i) + 1 =
      rootInversionCount P b w := by
  have hpos := (simpleWeylReflection_sign_flip P b w i).mpr hneg
  simpa only [mul_assoc, simpleWeylReflection_mul_self, mul_one] using
    (rootInversionCount_mul_simple_of_positive P b
      (w * simpleWeylReflection P b i) i hpos).symm

@[simp] theorem rootWeylLength_one : rootWeylLength P b 1 = 0 := by
  exact Nat.eq_zero_of_le_zero (rootWeylLength_le P b 1 [] (by rfl))

theorem rootWeylLength_eq_zero_iff (w : P.weylGroupToPerm.range) :
    rootWeylLength P b w = 0 ↔ w = 1 := by
  constructor
  · intro h
    obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec P b w
    have hnil : l = [] := List.length_eq_zero_iff.mp (hlen.trans h)
    subst l
    apply Subtype.ext
    change w.val = (1 : Equiv.Perm ι)
    simpa only [simpleReflectionWord_nil] using hl.symm
  · rintro rfl
    exact rootWeylLength_one P b

private theorem rootInversionCount_eq_length_of_word (l : List b.support)
    (w : P.weylGroupToPerm.range) (hw : simpleReflectionWord P b l = w.val) :
    rootInversionCount P b w = rootWeylLength P b w := by
  classical
  induction l using List.reverseRecOn generalizing w with
  | nil =>
    have hwone : w = 1 := by
      apply Subtype.ext
      change w.val = (1 : Equiv.Perm ι)
      simpa only [simpleReflectionWord_nil] using hw.symm
    subst w
    rw [rootInversionCount_one, rootWeylLength_one]
  | append_singleton l i ih =>
    let v := w * simpleWeylReflection P b i
    have hv : simpleReflectionWord P b l = v.val := by
      have hw' : simpleReflectionWord P b l * P.reflectionPerm i.val = w.val := by
        simpa only [simpleReflectionWord_append, simpleReflectionWord_cons,
          simpleReflectionWord_nil, mul_one] using hw
      change simpleReflectionWord P b l = w.val * P.reflectionPerm i.val
      rw [← hw', mul_assoc]
      have hs : P.reflectionPerm i.val * P.reflectionPerm i.val = 1 := by
        simpa only [pow_two] using P.reflectionPerm_sq i.val
      rw [hs, mul_one]
    have hvw : v * simpleWeylReflection P b i = w := by
      dsimp only [v]
      rw [mul_assoc, simpleWeylReflection_mul_self, mul_one]
    have hi := ih v hv
    by_cases hpos : b.IsPos (v.val i.val)
    · have hc := rootInversionCount_mul_simple_of_positive P b v i hpos
      have hl := rootWeylLength_mul_simple_of_positive P b v i hpos
      rw [hvw] at hc hl
      omega
    · have hc := rootInversionCount_mul_simple_of_negative P b v i hpos
      have hl := rootWeylLength_mul_simple_of_negative P b v i hpos
      rw [hvw] at hc hl
      omega

/-- Actual minimum word length is exactly the number of positive roots made
negative. No abstract Coxeter length or presentation is used. -/
theorem rootInversionCount_eq_rootWeylLength (w : P.weylGroupToPerm.range) :
    rootInversionCount P b w = rootWeylLength P b w := by
  obtain ⟨l, hl⟩ := exists_simpleReflectionWord_of_mem P b w.property
  exact rootInversionCount_eq_length_of_word P b l w hl

theorem rootInversionCount_eq_zero_iff (w : P.weylGroupToPerm.range) :
    rootInversionCount P b w = 0 ↔ w = 1 := by
  rw [rootInversionCount_eq_rootWeylLength, rootWeylLength_eq_zero_iff]

/-- A Weyl permutation preserving all positive roots is the identity. -/
theorem rootWeyl_preserves_positive_iff_one (w : P.weylGroupToPerm.range) :
    (∀ β : ι, b.IsPos β → b.IsPos (w.val β)) ↔ w = 1 := by
  constructor
  · intro hpos
    apply (rootInversionCount_eq_zero_iff P b w).mp
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro β hβ
    obtain ⟨hp, hn⟩ := (mem_rootInversions P b w β).mp hβ
    exact hn (hpos β hp)
  · rintro rfl
    intro β hβ
    exact hβ

theorem rootWeylLength_le_card_positive (w : P.weylGroupToPerm.range) :
    rootWeylLength P b w ≤ (Finset.univ.filter (fun β : ι => b.IsPos β)).card := by
  classical
  rw [← rootInversionCount_eq_rootWeylLength]
  apply Finset.card_le_card
  intro β hβ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ β, ((mem_rootInversions P b w β).mp hβ).1⟩

end Atlas.Chevalley.RootData

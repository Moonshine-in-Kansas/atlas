import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionLength

/-! Reduced words in the actual root-permutation Weyl image. No abstract
Coxeter-system identification is used. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- An actual simple word, bundled in the Weyl image. -/
def rootWeylWord (l : List b.support) : P.weylGroupToPerm.range :=
  (l.map (simpleWeylReflection P b)).prod

@[simp] theorem rootWeylWord_val (l : List b.support) :
    (rootWeylWord P b l).val = simpleReflectionWord P b l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (P.reflectionPerm i.val * (rootWeylWord P b l).val) = _
    rw [ih, simpleReflectionWord_cons]

@[simp] theorem rootWeylWord_append (l r : List b.support) :
    rootWeylWord P b (l ++ r) = rootWeylWord P b l * rootWeylWord P b r := by
  simp only [rootWeylWord, List.map_append, List.prod_append]

@[simp] theorem rootWeylWord_reverse (l : List b.support) :
    rootWeylWord P b l.reverse = (rootWeylWord P b l)⁻¹ := by
  apply Subtype.ext
  change (rootWeylWord P b l.reverse).val = (rootWeylWord P b l).val⁻¹
  rw [rootWeylWord_val, rootWeylWord_val, simpleReflectionWord_reverse]

private theorem rootWeylLength_inv_le (w : P.weylGroupToPerm.range) :
    rootWeylLength P b w⁻¹ ≤ rootWeylLength P b w := by
  obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec P b w
  have h := rootWeylLength_le P b w⁻¹ l.reverse (by
    change simpleReflectionWord P b l.reverse = w.val⁻¹
    rw [simpleReflectionWord_reverse, hl])
  simpa only [List.length_reverse, hlen] using h

@[simp] theorem rootWeylLength_inv (w : P.weylGroupToPerm.range) :
    rootWeylLength P b w⁻¹ = rootWeylLength P b w := by
  apply le_antisymm (rootWeylLength_inv_le P b w)
  simpa only [inv_inv] using rootWeylLength_inv_le P b w⁻¹

theorem rootWeylLength_mul_le (w v : P.weylGroupToPerm.range) :
    rootWeylLength P b (w * v) ≤ rootWeylLength P b w + rootWeylLength P b v := by
  obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec P b w
  obtain ⟨r, hrlen, hr⟩ := rootWeylLength_spec P b v
  have h := rootWeylLength_le P b (w * v) (l ++ r) (by
    change simpleReflectionWord P b (l ++ r) = w.val * v.val
    rw [simpleReflectionWord_append, hl, hr])
  simpa only [List.length_append, hlen, hrlen] using h

/-- A word is reduced when it achieves the actual minimum length. -/
def IsReducedRootWord (l : List b.support) : Prop :=
  rootWeylLength P b (rootWeylWord P b l) = l.length

theorem rootWeylWord_length_le (l : List b.support) :
    rootWeylLength P b (rootWeylWord P b l) ≤ l.length :=
  rootWeylLength_le P b (rootWeylWord P b l) l (rootWeylWord_val P b l).symm

theorem isReducedRootWord_reverse_iff (l : List b.support) :
    IsReducedRootWord P b l.reverse ↔ IsReducedRootWord P b l := by
  simp only [IsReducedRootWord, rootWeylWord_reverse, rootWeylLength_inv,
    List.length_reverse]

/-- Every prefix and suffix of a minimum word is a minimum word. -/
theorem isReducedRootWord_append_parts (l r : List b.support)
    (h : IsReducedRootWord P b (l ++ r)) :
    IsReducedRootWord P b l ∧ IsReducedRootWord P b r := by
  have h1 := rootWeylWord_length_le P b l
  have h2 := rootWeylWord_length_le P b r
  have h3 := rootWeylLength_mul_le P b (rootWeylWord P b l) (rootWeylWord P b r)
  dsimp only [IsReducedRootWord] at h ⊢
  rw [rootWeylWord_append, List.length_append] at h
  constructor <;> omega

theorem isReducedRootWord_take (l : List b.support)
    (h : IsReducedRootWord P b l) (n : ℕ) :
    IsReducedRootWord P b (l.take n) := by
  have hh : IsReducedRootWord P b (l.take n ++ l.drop n) := by
    simpa only [List.take_append_drop] using h
  exact (isReducedRootWord_append_parts P b _ _ hh).1

theorem isReducedRootWord_drop (l : List b.support)
    (h : IsReducedRootWord P b l) (n : ℕ) :
    IsReducedRootWord P b (l.drop n) := by
  have hh : IsReducedRootWord P b (l.take n ++ l.drop n) := by
    simpa only [List.take_append_drop] using h
  exact (isReducedRootWord_append_parts P b _ _ hh).2

end Atlas.Chevalley.RootData

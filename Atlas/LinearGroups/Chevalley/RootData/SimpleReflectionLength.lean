import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionExchange

/-! Shortest words and sign-controlled descent in the actual root-permutation
Weyl image. No Coxeter presentation or linear-group kernel is assumed. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

theorem simpleReflectionWord_reverse (l : List b.support) :
    simpleReflectionWord P b l.reverse = (simpleReflectionWord P b l)⁻¹ := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.reverse_cons, simpleReflectionWord_append,
      simpleReflectionWord_cons, simpleReflectionWord_nil, mul_one,
      mul_inv_rev, P.reflectionPerm_inv, ih]

theorem exists_simpleReflectionWord_of_mem {w : Equiv.Perm ι}
    (hw : w ∈ P.weylGroupToPerm.range) :
    ∃ l : List b.support, simpleReflectionWord P b l = w := by
  rw [← simpleReflectionClosure_eq_weylImage P b] at hw
  induction hw using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    exact ⟨[i], by simp⟩
  | one => exact ⟨[], rfl⟩
  | mul g h hg hh ihg ihh =>
    obtain ⟨l, rfl⟩ := ihg
    obtain ⟨r, rfl⟩ := ihh
    exact ⟨l ++ r, simpleReflectionWord_append P b l r⟩
  | inv g hg ih =>
    obtain ⟨l, rfl⟩ := ih
    exact ⟨l.reverse, simpleReflectionWord_reverse P b l⟩

private theorem exists_rootWeylWordLength (w : P.weylGroupToPerm.range) :
    ∃ n : ℕ, ∃ l : List b.support,
      l.length = n ∧ simpleReflectionWord P b l = w.val := by
  obtain ⟨l, hl⟩ := exists_simpleReflectionWord_of_mem P b w.property
  exact ⟨l.length, l, rfl, hl⟩

/-- Minimum length in the actual root-permutation Weyl image. -/
def rootWeylLength (w : P.weylGroupToPerm.range) : ℕ :=
  Nat.find (exists_rootWeylWordLength P b w)

theorem rootWeylLength_spec (w : P.weylGroupToPerm.range) :
    ∃ l : List b.support,
      l.length = rootWeylLength P b w ∧ simpleReflectionWord P b l = w.val :=
  Nat.find_spec (exists_rootWeylWordLength P b w)

theorem rootWeylLength_le (w : P.weylGroupToPerm.range) (l : List b.support)
    (hl : simpleReflectionWord P b l = w.val) :
    rootWeylLength P b w ≤ l.length :=
  Nat.find_min' (exists_rootWeylWordLength P b w) ⟨l, rfl, hl⟩

def simpleWeylReflection (i : b.support) : P.weylGroupToPerm.range :=
  ⟨P.reflectionPerm i.val, by
    rw [← simpleReflectionClosure_eq_weylImage P b]
    exact Subgroup.subset_closure ⟨i, rfl⟩⟩

@[simp] theorem simpleWeylReflection_mul_self (i : b.support) :
    simpleWeylReflection P b i * simpleWeylReflection P b i = 1 := by
  apply Subtype.ext
  exact P.reflectionPerm_sq i.val

theorem rootWeylLength_mul_simple_le (w : P.weylGroupToPerm.range)
    (i : b.support) :
    rootWeylLength P b (w * simpleWeylReflection P b i) ≤ rootWeylLength P b w + 1 := by
  obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec P b w
  have h := rootWeylLength_le P b (w * simpleWeylReflection P b i) (l ++ [i])
    (by
      change simpleReflectionWord P b (l ++ [i]) = w.val * P.reflectionPerm i.val
      simp only [simpleReflectionWord_append, simpleReflectionWord_cons,
        simpleReflectionWord_nil, mul_one, hl])
  simpa only [List.length_append, List.length_singleton, hlen] using h

theorem rootWeylLength_le_mul_simple_add_one (w : P.weylGroupToPerm.range)
    (i : b.support) :
    rootWeylLength P b w ≤ rootWeylLength P b (w * simpleWeylReflection P b i) + 1 := by
  simpa only [mul_assoc, simpleWeylReflection_mul_self, mul_one] using
    rootWeylLength_mul_simple_le P b (w * simpleWeylReflection P b i) i

/-- Exchange applied to a shortest actual word gives exact descent. -/
theorem rootWeylLength_mul_simple_of_negative (w : P.weylGroupToPerm.range)
    (i : b.support) (hneg : ¬ b.IsPos (w.val i.val)) :
    rootWeylLength P b (w * simpleWeylReflection P b i) + 1 = rootWeylLength P b w := by
  obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec P b w
  obtain ⟨l₁, j, l₂, hsplit, hex⟩ := simpleReflectionWord_exchange P b
    (b.isPos_of_mem_support i.property) l (by simpa only [hl] using hneg)
  have hle := rootWeylLength_le P b (w * simpleWeylReflection P b i) (l₁ ++ l₂)
    (by
      change simpleReflectionWord P b (l₁ ++ l₂) = w.val * P.reflectionPerm i.val
      simpa only [hl] using hex.symm)
  have hge := rootWeylLength_le_mul_simple_add_one P b w i
  simp only [hsplit, List.length_append, List.length_cons] at hlen hle
  omega

theorem simpleWeylReflection_sign_flip (w : P.weylGroupToPerm.range)
    (i : b.support) :
    b.IsPos ((w * simpleWeylReflection P b i).val i.val) ↔ ¬ b.IsPos (w.val i.val) := by
  obtain ⟨l, hl⟩ := exists_simpleReflectionWord_of_mem P b w.property
  have hc := simpleReflectionWord_conjugate P b l i.val
  rw [hl] at hc
  have hroot : (w * simpleWeylReflection P b i).val i.val =
      P.reflectionPerm (w.val i.val) (w.val i.val) := by
    change w.val (P.reflectionPerm i.val i.val) = _
    rw [hc]
    simp
  rw [hroot]
  exact RootPairing.Base.IsPos.neg_iff_not b (w.val i.val)

theorem rootWeylLength_mul_simple_of_positive (w : P.weylGroupToPerm.range)
    (i : b.support) (hpos : b.IsPos (w.val i.val)) :
    rootWeylLength P b (w * simpleWeylReflection P b i) = rootWeylLength P b w + 1 := by
  have hneg : ¬ b.IsPos ((w * simpleWeylReflection P b i).val i.val) :=
    fun h => ((simpleWeylReflection_sign_flip P b w i).mp h) hpos
  simpa only [mul_assoc, simpleWeylReflection_mul_self, mul_one] using
    (rootWeylLength_mul_simple_of_negative P b (w * simpleWeylReflection P b i) i hneg).symm

theorem rootWeylLength_mul_simple_lt_iff (w : P.weylGroupToPerm.range)
    (i : b.support) :
    rootWeylLength P b (w * simpleWeylReflection P b i) < rootWeylLength P b w ↔
      ¬ b.IsPos (w.val i.val) := by
  by_cases hpos : b.IsPos (w.val i.val)
  · rw [rootWeylLength_mul_simple_of_positive P b w i hpos]
    simp [hpos]
  · have h := rootWeylLength_mul_simple_of_negative P b w i hpos
    constructor
    · intro _; exact hpos
    · intro _; omega

end Atlas.Chevalley.RootData

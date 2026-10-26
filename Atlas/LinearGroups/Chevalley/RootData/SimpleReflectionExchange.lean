import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionGeneration
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum

/-! Actual root signs and deletion of one letter from an actual reflection word.
This does not assume or construct a Coxeter presentation. -/

noncomputable section
namespace Atlas.Chevalley.RootData

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- A simple reflection sends its own simple root to a negative root. -/
theorem not_isPos_reflection_simple (i : b.support) :
    ¬ b.IsPos (P.reflectionPerm i.val i.val) := by
  have hh := b.height_reflectionPerm_self i.val
  change b.height (P.reflectionPerm i.val i.val) = -b.height i.val at hh
  have hi : b.height i.val = 1 :=
    RootPairing.Base.height_one_of_mem_support i.property
  rw [b.isPos_iff, hh, hi]
  norm_num

/-- Among positive roots, a simple reflection changes sign only at its own root. -/
theorem positive_reflection_negative_iff (i : b.support) {β : ι}
    (hβ : b.IsPos β) :
    ¬ b.IsPos (P.reflectionPerm i.val β) ↔ β = i.val := by
  constructor
  · intro hneg
    by_contra hne
    exact hneg (hβ.reflectionPerm i.property hne)
  · intro h
    subst β
    exact not_isPos_reflection_simple P b i

/-- The literal root-label permutation of a list of simple reflections. -/
def simpleReflectionWord (l : List b.support) : Equiv.Perm ι :=
  (l.map (fun i => P.reflectionPerm i.val)).prod

@[simp] theorem simpleReflectionWord_nil :
    simpleReflectionWord P b [] = 1 := rfl

@[simp] theorem simpleReflectionWord_cons (i : b.support) (l : List b.support) :
    simpleReflectionWord P b (i :: l) =
      P.reflectionPerm i.val * simpleReflectionWord P b l := by
  simp only [simpleReflectionWord, List.map_cons, List.prod_cons]

@[simp] theorem simpleReflectionWord_append (l₁ l₂ : List b.support) :
    simpleReflectionWord P b (l₁ ++ l₂) =
      simpleReflectionWord P b l₁ * simpleReflectionWord P b l₂ := by
  simp only [simpleReflectionWord, List.map_append, List.prod_append]

/-- Conjugation of a root reflection by a literal word is the reflection in
its actual image root. This is only a root-label identity. -/
theorem simpleReflectionWord_conjugate (l : List b.support) (β : ι) :
    P.reflectionPerm (simpleReflectionWord P b l β) =
      simpleReflectionWord P b l * P.reflectionPerm β *
        (simpleReflectionWord P b l)⁻¹ := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [simpleReflectionWord_cons, Equiv.Perm.mul_apply]
    rw [reflectionPerm_conjugate P (simpleReflectionWord P b l β) i.val, ih]
    simp only [mul_inv_rev, P.reflectionPerm_inv]
    group

/-- Following a positive root through a word that makes it negative, one
letter acts on its own simple root. The suffix and that letter are retained. -/
theorem positive_to_negative_word_split {β : ι} (hβ : b.IsPos β)
    (l : List b.support) :
    ¬ b.IsPos (simpleReflectionWord P b l β) →
      ∃ l₁ : List b.support, ∃ i : b.support, ∃ l₂ : List b.support,
        l = l₁ ++ i :: l₂ ∧ simpleReflectionWord P b l₂ β = i.val := by
  induction l with
  | nil =>
    intro hneg
    exact False.elim (hneg (by simpa using hβ))
  | cons i l ih =>
    intro hneg
    by_cases hp : b.IsPos (simpleReflectionWord P b l β)
    · have hs : ¬ b.IsPos (P.reflectionPerm i.val (simpleReflectionWord P b l β)) := by
        simpa only [simpleReflectionWord_cons, Equiv.Perm.mul_apply] using hneg
      exact ⟨[], i, l, rfl, (positive_reflection_negative_iff P b i hp).mp hs⟩
    · obtain ⟨l₁, j, l₂, hl, hr⟩ := ih hp
      refine ⟨i :: l₁, j, l₂, ?_, hr⟩
      simp only [List.cons_append, hl]

/-- Actual reflection-word exchange: if a positive root becomes negative,
right multiplication by its reflection deletes one letter. No reduced-word
or Coxeter-system hypothesis occurs. This does not yet identify relations in
an abstract presentation or in the companion torus quotient. -/
theorem simpleReflectionWord_exchange {β : ι} (hβ : b.IsPos β)
    (l : List b.support) (hneg : ¬ b.IsPos (simpleReflectionWord P b l β)) :
    ∃ l₁ : List b.support, ∃ i : b.support, ∃ l₂ : List b.support,
      l = l₁ ++ i :: l₂ ∧
      simpleReflectionWord P b l * P.reflectionPerm β =
        simpleReflectionWord P b (l₁ ++ l₂) := by
  obtain ⟨l₁, i, l₂, hl, hr⟩ := positive_to_negative_word_split P b hβ l hneg
  refine ⟨l₁, i, l₂, hl, ?_⟩
  have hc : P.reflectionPerm i.val = simpleReflectionWord P b l₂ *
      P.reflectionPerm β * (simpleReflectionWord P b l₂)⁻¹ := by
    simpa only [hr] using simpleReflectionWord_conjugate P b l₂ β
  have hs : P.reflectionPerm β * P.reflectionPerm β = 1 := by
    simpa only [pow_two] using P.reflectionPerm_sq β
  rw [hl, simpleReflectionWord_append, simpleReflectionWord_cons,
    simpleReflectionWord_append, hc]
  calc
    _ = (simpleReflectionWord P b l₁ * simpleReflectionWord P b l₂) *
        (P.reflectionPerm β * P.reflectionPerm β) := by group
    _ = _ := by rw [hs, mul_one]

end Atlas.Chevalley.RootData

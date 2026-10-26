import Atlas.LinearGroups.Chevalley.RootData.G2
import Atlas.LinearGroups.Chevalley.RootData.DominantFunctionalStabilizer
import Atlas.LinearGroups.Chevalley.RootData.ParabolicCosetDecomposition
import Mathlib.Tactic.FinCases

/-! A six-point orbit in the actual G2 Weyl permutation image. Its stabilizer
is the actual rank-one parabolic, proved from a dominant lattice functional.
Only root labels and six short word representatives are enumerated. -/
noncomputable section
namespace Atlas.Chevalley.G2Parabolic
open Classical RootData

abbrev W := G2Data.pairing.weylGroupToPerm.range
abbrev simple (i : Fin 2) := G2Data.baseIndexEquiv i
def J : Finset G2Data.base.support := {simple 1}

def functional : G2Data.pairing.rootSpan ℤ →+ ℚ where
  toFun x := (x.val 0 : ℚ)
  map_zero' := by simp
  map_add' x y := by simp

theorem functional_simple (i : Fin 2) :
    functional (G2Data.pairing.rootSpanMem ℤ (simple i).val) =
      if i = 0 then 1 else 0 := by
  fin_cases i <;> rfl

private theorem functional_dominant (i : G2Data.base.support) :
    0 ≤ functional (G2Data.pairing.rootSpanMem ℤ i.val) := by
  obtain ⟨j, rfl⟩ := G2Data.baseIndexEquiv.surjective i
  rw [functional_simple]
  split_ifs <;> norm_num

private theorem functional_zero_simple :
    rootFunctionalZeroSimple G2Data.pairing G2Data.base functional = J := by
  ext i
  obtain ⟨j, rfl⟩ := G2Data.baseIndexEquiv.surjective i
  simp only [rootFunctionalZeroSimple, Finset.mem_filter, Finset.mem_univ, true_and,
    J, Finset.mem_singleton, functional_simple, G2Data.baseIndexEquiv.injective.eq_iff]
  fin_cases j <;> norm_num

private theorem functional_root (β : G2Data.Root) :
    functional (G2Data.pairing.rootSpanMem ℤ β) =
      (G2Data.pairing.pairing β 7 : ℚ) := by
  change (G2Table.coordinates β 0 : ℚ) =
    (G2Table.dot (G2Table.dualCoordinates 7) (G2Table.coordinates β) : ℚ)
  have h : G2Table.coordinates β 0 =
      G2Table.dot (G2Table.dualCoordinates 7) (G2Table.coordinates β) := by
    exact (show ∀ β : G2Table.Root, G2Table.coordinates β 0 =
      G2Table.dot (G2Table.dualCoordinates 7) (G2Table.coordinates β) from by decide +kernel) β
  exact congrArg (fun n : ℤ => (n : ℚ)) h

private theorem word_pairing (l : List G2Data.base.support) (α β : G2Data.Root) :
    G2Data.pairing.pairing (simpleReflectionWord G2Data.pairing G2Data.base l α)
      (simpleReflectionWord G2Data.pairing G2Data.base l β) =
        G2Data.pairing.pairing α β := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [simpleReflectionWord_cons, Equiv.Perm.mul_apply]
    rw [G2Data.pairing.pairing_reflectionPerm, G2Data.pairing.reflectionPerm_self]
    exact ih

private theorem weyl_pairing (w : W) (α β : G2Data.Root) :
    G2Data.pairing.pairing (w.val α) (w.val β) = G2Data.pairing.pairing α β := by
  obtain ⟨l, hl⟩ := exists_simpleReflectionWord_of_mem G2Data.pairing G2Data.base w.property
  simpa only [hl] using word_pairing l α β

private theorem pairing_detects_seed (β : G2Data.Root)
    (h : ∀ α, G2Data.pairing.pairing α β = G2Data.pairing.pairing α 7) : β = 7 := by
  have hc : ∀ β : G2Table.Root,
      (∀ α : G2Table.Root, G2Table.dot (G2Table.dualCoordinates β) (G2Table.coordinates α) =
        G2Table.dot (G2Table.dualCoordinates 7) (G2Table.coordinates α)) → β = 7 := by
    decide +kernel
  exact hc β h

/-- The actual stabilizer of the dominant coroot label 7 is the rank-one parabolic. -/
theorem fixes_seed_iff_parabolic (w : W) :
    w.val 7 = 7 ↔ w ∈ rootParabolicSubgroup G2Data.pairing G2Data.base J := by
  have heq := rootFunctionalStabilizer_eq_parabolic G2Data.pairing G2Data.base
    functional functional_dominant
  rw [functional_zero_simple] at heq
  rw [← heq]
  constructor
  · intro hw β
    rw [functional_root, functional_root]
    exact congrArg (fun n : ℤ => (n : ℚ)) (by
      simpa only [hw] using weyl_pairing w β 7)
  · intro hw
    apply pairing_detects_seed
    intro α
    have hfun := hw ((w⁻¹).val α)
    have hinv : w.val ((w⁻¹).val α) = α := w.val.apply_symm_apply α
    rw [functional_root, functional_root, hinv] at hfun
    have hcast : G2Data.pairing.pairing α 7 =
        G2Data.pairing.pairing ((w⁻¹).val α) 7 := Int.cast_injective hfun
    have hp := weyl_pairing w ((w⁻¹).val α) 7
    rw [hinv] at hp
    exact hp.trans hcast.symm

/-- The six orbit labels, ordered by the lengths of the representatives below. -/
def orbitLabel : Fin 6 → G2Data.Root := ![7, 3, 0, 2, 6, 10]

def orbitWord : Fin 6 → List (Fin 2) :=
  ![[], [0], [1, 0], [0, 1, 0], [1, 0, 1, 0], [0, 1, 0, 1, 0]]

def orbitRepresentative (k : Fin 6) : W :=
  rootWeylWord G2Data.pairing G2Data.base ((orbitWord k).map simple)

def tableAction : List (Fin 2) → G2Data.Root → G2Data.Root
  | [], β => β
  | i :: l, β => G2Table.reflectionIndex (G2Table.simpleIndex i) (tableAction l β)

theorem orbitRepresentative_apply (k : Fin 6) (β : G2Data.Root) :
    (orbitRepresentative k).val β = tableAction (orbitWord k) β := by
  suffices ∀ l : List (Fin 2), ∀ β : G2Data.Root,
      (rootWeylWord G2Data.pairing G2Data.base (l.map simple)).val β = tableAction l β by
    exact this (orbitWord k) β
  intro l
  induction l with
  | nil => intro β; rfl
  | cons i l ih =>
    intro β
    change G2Table.reflectionIndex (G2Table.simpleIndex i)
      ((rootWeylWord G2Data.pairing G2Data.base (l.map simple)).val β) = _
    rw [ih]
    rfl

theorem orbitRepresentative_seed (k : Fin 6) :
    (orbitRepresentative k).val 7 = orbitLabel k := by
  rw [orbitRepresentative_apply]
  exact (show ∀ k : Fin 6, tableAction (orbitWord k) 7 = orbitLabel k from by decide +kernel) k

theorem orbitLabel_injective : Function.Injective orbitLabel := by decide +kernel

/-- The orbit is exhausted using closure of six root labels under the two generators. -/
theorem exists_orbitLabel (w : W) : ∃ k : Fin 6, w.val 7 = orbitLabel k := by
  have hclosed : ∀ i : Fin 2, ∀ k : Fin 6, ∃ j : Fin 6,
      G2Table.reflectionIndex (G2Table.simpleIndex i) (orbitLabel k) = orbitLabel j := by
    decide +kernel
  have hword : ∀ l : List G2Data.base.support, ∀ k : Fin 6, ∃ j : Fin 6,
      simpleReflectionWord G2Data.pairing G2Data.base l (orbitLabel k) = orbitLabel j := by
    intro l
    induction l with
    | nil => intro k; exact ⟨k, rfl⟩
    | cons i l ih =>
      intro k
      obtain ⟨j, hj⟩ := ih k
      obtain ⟨a, rfl⟩ := G2Data.baseIndexEquiv.surjective i
      obtain ⟨t, ht⟩ := hclosed a j
      refine ⟨t, ?_⟩
      simp only [simpleReflectionWord_cons, Equiv.Perm.mul_apply, hj]
      exact ht
  obtain ⟨l, hl⟩ := exists_simpleReflectionWord_of_mem G2Data.pairing G2Data.base w.property
  obtain ⟨k, hk⟩ := hword l 0
  exact ⟨k, by simpa only [hl, orbitLabel, Matrix.cons_val_zero] using hk⟩

end Atlas.Chevalley.G2Parabolic

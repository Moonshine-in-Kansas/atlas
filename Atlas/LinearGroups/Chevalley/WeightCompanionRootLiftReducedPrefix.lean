import Atlas.LinearGroups.Chevalley.WeightCompanionRootLiftCoherence
import Atlas.LinearGroups.Chevalley.WeightCompanionRootMarks
import Atlas.LinearGroups.Chevalley.WeightCompanionTitsLift

/-! An arbitrary retained positive-root witness reduces to a literal reduced
prefix. Only equality of its entire Weyl permutation is used to compare lifts.
Root-subgroup independence under different permutations is not assumed. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData Atlas.GroupTheory
open Atlas.GroupTheory.ReducedWords

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

/-- Evaluating paired generators keeps the actual permutation and matrix word. -/
theorem weightCompanionMarkedWeyl_wordEval (p : List b.support) :
    wordEval (weightCompanionMarkedWeyl P b O hc hm R) p =
      ((rootWeylWord P b p).val,
        wordEval (fun i => weightCompanionWeyl P b O hc hm R i 1) p) := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    change (P.reflectionPerm i.val, weightCompanionWeyl P b O hc hm R i 1) *
      wordEval (weightCompanionMarkedWeyl P b O hc hm R) p =
      (P.reflectionPerm i.val * (rootWeylWord P b p).val,
        weightCompanionWeyl P b O hc hm R i 1 *
          wordEval (fun j => weightCompanionWeyl P b O hc hm R j 1) p)
    rw [ih]
    rfl

variable [Nontrivial R]

/-- Replacing the whole Weyl permutation by any representing word preserves
the retained root subgroup. Reducedness and positivity are unnecessary here. -/
theorem weightCompanionRootLiftSubgroup_eq_wordEval
    (hdiamond : SimpleDiamondProducts P b) {β : ι}
    (L : WeightCompanionRootLift P b O hc hm R β) (p : List b.support)
    (hperm : (rootWeylWord P b p).val =
      weightCompanionNRootPermHom P b O hc hm R L.lift) :
    weightCompanionRootLiftSubgroup P b O hc hm R L =
      conjugateSubgroup
        (wordEval (fun i => weightCompanionWeyl P b O hc hm R i 1) p)
        (weightCompanionXHom P b O hc hm R L.simple).range := by
  let L' : WeightCompanionRootLift P b O hc hm R β :=
    { simple := L.simple
      lift := wordEval (weightCompanionSimpleWeylInN P b O hc hm R) p
      root_eq := by
        rw [weightCompanionNRootPermHom_wordEval, hperm]
        exact L.root_eq }
  have heq : weightCompanionNRootPermHom P b O hc hm R L.lift =
      weightCompanionNRootPermHom P b O hc hm R L'.lift := by
    change weightCompanionNRootPermHom P b O hc hm R L.lift =
      weightCompanionNRootPermHom P b O hc hm R
        (wordEval (weightCompanionSimpleWeylInN P b O hc hm R) p)
    rw [weightCompanionNRootPermHom_wordEval, hperm]
  calc
    weightCompanionRootLiftSubgroup P b O hc hm R L =
        weightCompanionRootLiftSubgroup P b O hc hm R L' :=
      weightCompanionRootLiftSubgroup_eq_of_same_rootPermutation
        P b O hc hm R hdiamond L L' rfl heq
    _ = _ := by
      change ((MulAut.conj
        (wordEval (weightCompanionSimpleWeylInN P b O hc hm R) p).val).toMonoidHom.comp
          (weightCompanionXHom P b O hc hm R L.simple)).range = _
      rw [← conjugateSubgroup_range, weightCompanionSimpleWeylInN_wordEval_val]

/-- The preceding equality retains the root label as well as the subgroup. -/
theorem weightCompanionRootLift_mark_eq_wordEval
    (hdiamond : SimpleDiamondProducts P b) {β : ι}
    (L : WeightCompanionRootLift P b O hc hm R β) (p : List b.support)
    (hperm : (rootWeylWord P b p).val =
      weightCompanionNRootPermHom P b O hc hm R L.lift) :
    (β, weightCompanionRootLiftSubgroup P b O hc hm R L) =
      labelledSubgroupAction
        (wordEval (weightCompanionMarkedWeyl P b O hc hm R) p)
        (weightCompanionSimpleRootMark P b O hc hm R L.simple) := by
  rw [weightCompanionMarkedWeyl_wordEval]
  apply Prod.ext
  · change β = (rootWeylWord P b p).val L.simple.val
    rw [hperm, L.root_eq]
  · exact weightCompanionRootLiftSubgroup_eq_wordEval P b O hc hm R
      hdiamond L p hperm

/-- A positive retained witness is a reduced-prefix mark. Choose a shortest
word for its full Weyl permutation; positivity makes appending the originating
simple reflection increase length. There is no chamber-stabilizer premise. -/
theorem weightCompanionRootLift_reducedPrefix
    (hdiamond : SimpleDiamondProducts P b) {β : ι} (hβ : b.IsPos β)
    (L : WeightCompanionRootLift P b O hc hm R β) :
    ∃ p : List b.support,
      IsReducedRootWord P b p ∧
      IsReducedRootWord P b (p ++ [L.simple]) ∧
      (rootWeylWord P b p).val = weightCompanionNRootPermHom P b O hc hm R L.lift ∧
      (β, weightCompanionRootLiftSubgroup P b O hc hm R L) =
        labelledSubgroupAction
          (wordEval (weightCompanionMarkedWeyl P b O hc hm R) p)
          (weightCompanionSimpleRootMark P b O hc hm R L.simple) := by
  let w : P.weylGroupToPerm.range :=
    ⟨weightCompanionNRootPermHom P b O hc hm R L.lift, by
      rw [← weightCompanionNRootPermHom_range_eq_weylImage P b O hc hm R]
      exact ⟨L.lift, rfl⟩⟩
  obtain ⟨p, hlen, hp⟩ := rootWeylLength_spec P b w
  have hpw : rootWeylWord P b p = w := by
    apply Subtype.ext
    rw [rootWeylWord_val, hp]
  have hperm : (rootWeylWord P b p).val =
      weightCompanionNRootPermHom P b O hc hm R L.lift := by
    rw [hpw]
  have hred : IsReducedRootWord P b p := by
    change rootWeylLength P b (rootWeylWord P b p) = p.length
    rw [hpw, hlen]
  have hpos : b.IsPos (w.val L.simple.val) := by
    change b.IsPos (weightCompanionNRootPermHom P b O hc hm R L.lift L.simple.val)
    rw [L.root_eq]
    exact hβ
  have hword : rootWeylWord P b (p ++ [L.simple]) =
      w * simpleWeylReflection P b L.simple := by
    rw [rootWeylWord_append, hpw]
    simp only [rootWeylWord, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
  have hred' : IsReducedRootWord P b (p ++ [L.simple]) := by
    change rootWeylLength P b (rootWeylWord P b (p ++ [L.simple])) =
      (p ++ [L.simple]).length
    rw [hword, rootWeylLength_mul_simple_of_positive P b w L.simple hpos,
      List.length_append, List.length_singleton, hlen]
  exact ⟨p, hred, hred', hperm,
    weightCompanionRootLift_mark_eq_wordEval P b O hc hm R hdiamond L p hperm⟩

/-- The arbitrary witness occurs in an actual reduced marked word, so a later
longest-word uniqueness theorem can be applied without a further lift premise. -/
theorem weightCompanionRootLift_mem_reducedMarkedWordSet
    (hdiamond : SimpleDiamondProducts P b) {β : ι} (hβ : b.IsPos β)
    (L : WeightCompanionRootLift P b O hc hm R β) :
    ∃ p : List b.support,
      IsReducedRootWord P b p ∧ IsReducedRootWord P b (p ++ [L.simple]) ∧
      (rootWeylWord P b p).val = weightCompanionNRootPermHom P b O hc hm R L.lift ∧
      (β, weightCompanionRootLiftSubgroup P b O hc hm R L) ∈
        weightCompanionMarkedWordSet P b O hc hm R (p ++ [L.simple]) := by
  obtain ⟨p, hp, hpi, hperm, hmark⟩ :=
    weightCompanionRootLift_reducedPrefix P b O hc hm R hdiamond hβ L
  refine ⟨p, hp, hpi, hperm, ?_⟩
  rw [hmark]
  exact prefix_mark_mem_markedWordSet
    (weightCompanionMarkedWeyl P b O hc hm R) labelledSubgroupAction
    (weightCompanionSimpleRootMark P b O hc hm R) p [] L.simple

end Atlas.Chevalley

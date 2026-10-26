import Atlas.LinearGroups.Chevalley.WeightCompanionTitsReducedWords
import Atlas.LinearGroups.Chevalley.RootData.RootInversionLength

/-! Canonical reduced Tits representatives in the actual full companion N.
They lift actual Weyl permutations and multiply when lengths add. This is a
set-theoretic section, not a homomorphism W → N or a root-coherence theorem. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData
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

/-- Evaluate one shortest representative of w in the actual N. Independence
of that choice follows below from the actual braid relations. -/
def weightCompanionTitsLift (w : P.weylGroupToPerm.range) :
    weightCompanionExtendedWeylSubgroup P b O hc hm R :=
  wordEval (weightCompanionSimpleWeylInN P b O hc hm R)
    (Classical.choose (root_reduced_representatives P b w))

/-- Any reduced representative computes the same actual Tits lift. -/
theorem weightCompanionTitsLift_eq_wordEval
    (hdiamond : SimpleDiamondProducts P b) (w : P.weylGroupToPerm.range)
    (l : List b.support) (heq : rootWeylWord P b l = w)
    (hred : IsReducedRootWord P b l) :
    weightCompanionTitsLift P b O hc hm R w =
      wordEval (weightCompanionSimpleWeylInN P b O hc hm R) l := by
  let r := Classical.choose (root_reduced_representatives P b w)
  have hs : rootWeylWord P b r = w ∧ r.length = rootWeylLength P b w :=
    Classical.choose_spec (root_reduced_representatives P b w)
  change wordEval (weightCompanionSimpleWeylInN P b O hc hm R) r = _
  apply weightCompanionSimpleWeylInN_reduced_wordEval_eq P b O hc hm R hdiamond
  · change rootWeylLength P b (rootWeylWord P b r) = r.length
    rw [hs.1, hs.2]
  · exact hred
  · exact hs.1.trans heq.symm

/-- The identity has the empty reduced lift, without a diamond premise. -/
@[simp] theorem weightCompanionTitsLift_one :
    weightCompanionTitsLift P b O hc hm R 1 = 1 := by
  have hs := Classical.choose_spec (root_reduced_representatives P b 1)
  have hnil : Classical.choose (root_reduced_representatives P b 1) = [] :=
    List.length_eq_zero_iff.mp (hs.2.trans (rootWeylLength_one P b))
  rw [weightCompanionTitsLift, hnil, wordEval_nil]

/-- The actual simple reflection lifts to its original literal Weyl operator. -/
theorem weightCompanionTitsLift_simple
    (hdiamond : SimpleDiamondProducts P b) (i : b.support) :
    weightCompanionTitsLift P b O hc hm R (simpleWeylReflection P b i) =
      weightCompanionSimpleWeylInN P b O hc hm R i := by
  have hpos : b.IsPos ((1 : P.weylGroupToPerm.range).val i.val) :=
    b.isPos_of_mem_support i.property
  have hlen : rootWeylLength P b (simpleWeylReflection P b i) = 1 := by
    simpa only [one_mul, rootWeylLength_one, zero_add] using
      rootWeylLength_mul_simple_of_positive P b 1 i hpos
  have hword : rootWeylWord P b [i] = simpleWeylReflection P b i := by
    simp only [rootWeylWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
  have hred : IsReducedRootWord P b [i] := by
    change rootWeylLength P b (rootWeylWord P b [i]) = 1
    rw [hword, hlen]
  simpa only [wordEval_singleton] using
    weightCompanionTitsLift_eq_wordEval P b O hc hm R hdiamond
      (simpleWeylReflection P b i) [i] hword hred

/-- Multiplication of canonical lifts holds when the actual Weyl lengths add.
No unrestricted multiplicativity is asserted. -/
theorem weightCompanionTitsLift_mul_of_length_add
    (hdiamond : SimpleDiamondProducts P b) (w v : P.weylGroupToPerm.range)
    (hlen : rootWeylLength P b (w * v) = rootWeylLength P b w + rootWeylLength P b v) :
    weightCompanionTitsLift P b O hc hm R (w * v) =
      weightCompanionTitsLift P b O hc hm R w *
        weightCompanionTitsLift P b O hc hm R v := by
  obtain ⟨l, hl, hll⟩ := root_reduced_representatives P b w
  obtain ⟨r, hr, hrl⟩ := root_reduced_representatives P b v
  change rootWeylWord P b l = w at hl
  change rootWeylWord P b r = v at hr
  have hredl : IsReducedRootWord P b l := by
    change rootWeylLength P b (rootWeylWord P b l) = l.length
    rw [hl, hll]
  have hredr : IsReducedRootWord P b r := by
    change rootWeylLength P b (rootWeylWord P b r) = r.length
    rw [hr, hrl]
  have hprod : rootWeylWord P b (l ++ r) = w * v := by
    rw [rootWeylWord_append, hl, hr]
  have hredprod : IsReducedRootWord P b (l ++ r) := by
    change rootWeylLength P b (rootWeylWord P b (l ++ r)) = (l ++ r).length
    rw [hprod, hlen, List.length_append, hll, hrl]
  calc
    weightCompanionTitsLift P b O hc hm R (w * v) =
        wordEval (weightCompanionSimpleWeylInN P b O hc hm R) (l ++ r) :=
      weightCompanionTitsLift_eq_wordEval P b O hc hm R hdiamond (w * v)
        (l ++ r) hprod hredprod
    _ = wordEval (weightCompanionSimpleWeylInN P b O hc hm R) l *
        wordEval (weightCompanionSimpleWeylInN P b O hc hm R) r :=
      wordEval_append _ l r
    _ = weightCompanionTitsLift P b O hc hm R w *
        weightCompanionTitsLift P b O hc hm R v := by
      rw [weightCompanionTitsLift_eq_wordEval P b O hc hm R hdiamond w l hl hredl,
        weightCompanionTitsLift_eq_wordEval P b O hc hm R hdiamond v r hr hredr]

variable [Nontrivial R]

/-- The actual N root-permutation action of a literal word is that root word. -/
theorem weightCompanionNRootPermHom_wordEval (l : List b.support) :
    weightCompanionNRootPermHom P b O hc hm R
        (wordEval (weightCompanionSimpleWeylInN P b O hc hm R) l) =
      (rootWeylWord P b l).val := by
  induction l with
  | nil => exact map_one (weightCompanionNRootPermHom P b O hc hm R)
  | cons i l ih =>
    change weightCompanionNRootPermHom P b O hc hm R
      (weightCompanionSimpleWeylInN P b O hc hm R i *
        wordEval (weightCompanionSimpleWeylInN P b O hc hm R) l) =
      P.reflectionPerm i.val * (rootWeylWord P b l).val
    rw [map_mul, weightCompanionNRootPermHom_simple, ih]

/-- The Tits lift is an actual section of the root-permutation action.
It does not require identification of that action's kernel with the torus. -/
theorem weightCompanionNRootPermHom_titsLift (w : P.weylGroupToPerm.range) :
    weightCompanionNRootPermHom P b O hc hm R
      (weightCompanionTitsLift P b O hc hm R w) = w.val := by
  rw [weightCompanionTitsLift, weightCompanionNRootPermHom_wordEval]
  have hs : rootWeylWord P b (Classical.choose (root_reduced_representatives P b w)) = w :=
    (Classical.choose_spec (root_reduced_representatives P b w)).1
  exact congrArg Subtype.val hs

/-- Distinct actual Weyl permutations have distinct chosen Tits lifts. This
is injectivity of a section, not injectivity of the full adjoint projection. -/
theorem weightCompanionTitsLift_injective :
    Function.Injective (weightCompanionTitsLift P b O hc hm R) := by
  intro w v heq
  apply Subtype.ext
  have he := congrArg (weightCompanionNRootPermHom P b O hc hm R) heq
  simpa only [weightCompanionNRootPermHom_titsLift] using he

end Atlas.Chevalley

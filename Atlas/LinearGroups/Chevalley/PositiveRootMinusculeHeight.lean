import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeylTransportedHeight
import Atlas.LinearGroups.Chevalley.WeightCompanionRootLiftCoherence
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionLength

/-! Every positive witnessed root family is unitriangular on every actual
minuscule block. The witness is retained; no same-target-only lift coherence
or injectivity of the full adjoint projection is assumed. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

/-- A literal simple Weyl word in the actual subgroup N. -/
def weightCompanionWeylWordInN : List b.support →
    weightCompanionExtendedWeylSubgroup P b O hc hm R
  | [] => 1
  | i :: l => weightCompanionSimpleWeylInN P b O hc hm R i *
      weightCompanionWeylWordInN l

/-- Every weight coordinate is the previously constructed literal matrix word. -/
theorem weightCompanionWeylWordInN_minuscule (l : List b.support) (k : κ) :
    (weightCompanionWeylWordInN P b O hc hm R l).val.val.2 k =
      weightOrbitWeylWord P b (O k) (hc k) (hm k) R l := by
  induction l with
  | nil => simp [weightCompanionWeylWordInN]
  | cons i l ih =>
    change (stringsOfWeightOrbit P (O k) (hc k) (hm k)).weylMatrixUnit R i.val 1 *
      (weightCompanionWeylWordInN P b O hc hm R l).val.val.2 k = _
    rw [ih, weightOrbitWeylWord_cons]

variable [Nontrivial R]

theorem weightCompanionWeylWordInN_rootPermutation (l : List b.support) :
    weightCompanionNRootPermHom P b O hc hm R
      (weightCompanionWeylWordInN P b O hc hm R l) = simpleReflectionWord P b l := by
  induction l with
  | nil => simp [weightCompanionWeylWordInN]
  | cons i l ih =>
    simp only [weightCompanionWeylWordInN, map_mul,
      weightCompanionNRootPermHom_simple, ih, simpleReflectionWord_cons]

/-- Positive triangularity for an arbitrary specified N witness. Equal full
Weyl permutations supply a unit rescaling of the same originating simple family. -/
theorem weightCompanion_rootLiftHom_minuscule_heightUnitriangular
    (hdiamond : SimpleDiamondProducts P b) {β : ι}
    (hβ : b.IsPos β) (L : WeightCompanionRootLift P b O hc hm R β)
    (k : κ) (t : Multiplicative R) :
    Atlas.Matrix.HeightUnitriangular
      (fun μ : WeightOrbit P (O k) => weightHeight P b μ.val)
      ((weightCompanionRootLiftHom P b O hc hm R L t).val.2 k).val := by
  have hn := weightCompanionNRootPerm_spec P b O hc hm R L.lift
  obtain ⟨l, hl⟩ := exists_simpleReflectionWord_of_mem P b
    (simpleRootPermutationSubgroup_le_weylImage P b hn.1)
  have he : weightCompanionNRootPermHom P b O hc hm R
      (weightCompanionWeylWordInN P b O hc hm R l) =
        weightCompanionNRootPermHom P b O hc hm R L.lift := by
    rw [weightCompanionWeylWordInN_rootPermutation]
    exact hl
  obtain ⟨a, ha⟩ := weightCompanion_rootConjugates_of_sameRootPermutation
    P b O hc hm R hdiamond L.simple
    (weightCompanionWeylWordInN P b O hc hm R l) L.lift he
  have hi : b.IsPos (simpleReflectionWord P b l L.simple.val) := by
    rw [hl]
    change b.IsPos (weightCompanionNRootPermHom P b O hc hm R L.lift L.simple.val)
    rw [L.root_eq]
    exact hβ
  rw [weightCompanionRootLiftHom_apply, ha t.toAdd]
  change Atlas.Matrix.HeightUnitriangular _
    ((weightCompanionWeylWordInN P b O hc hm R l).val.val.2 k *
      weightOrbitRootElement P (O k) (hc k) (hm k) R L.simple.val (-1) (by decide)
        (a.val * t.toAdd) *
      ((weightCompanionWeylWordInN P b O hc hm R l).val.val.2 k)⁻¹).val
  rw [weightCompanionWeylWordInN_minuscule]
  exact weightOrbitWeylWord_conjugate_root_heightUnitriangular P b
    (O k) (hc k) (hm k) R l L.simple hi (a.val * t.toAdd)

/-- Both the family and its inverse lie in the actual minuscule unitriangular subgroup. -/
theorem weightCompanion_rootLiftHom_minuscule_mem_heightUnitriangular
    (hdiamond : SimpleDiamondProducts P b) {β : ι}
    (hβ : b.IsPos β) (L : WeightCompanionRootLift P b O hc hm R β)
    (k : κ) (t : Multiplicative R) :
    (weightCompanionRootLiftHom P b O hc hm R L t).val.2 k ∈
      Atlas.Matrix.heightUnitriangularSubgroup
        (fun μ : WeightOrbit P (O k) => weightHeight P b μ.val) := by
  refine ⟨weightCompanion_rootLiftHom_minuscule_heightUnitriangular
    P b O hc hm R hdiamond hβ L k t, ?_⟩
  have hinv := weightCompanion_rootLiftHom_minuscule_heightUnitriangular
    P b O hc hm R hdiamond hβ L k t⁻¹
  have he : (weightCompanionRootLiftHom P b O hc hm R L t⁻¹).val.2 k =
      ((weightCompanionRootLiftHom P b O hc hm R L t).val.2 k)⁻¹ :=
    congrArg (fun g : WeightCompanion P b O hc hm R => g.val.2 k)
      (map_inv (weightCompanionRootLiftHom P b O hc hm R L) t)
  change Atlas.Matrix.HeightUnitriangular _
    (((weightCompanionRootLiftHom P b O hc hm R L t).val.2 k)⁻¹).val
  rw [← he]
  exact hinv

end Atlas.Chevalley

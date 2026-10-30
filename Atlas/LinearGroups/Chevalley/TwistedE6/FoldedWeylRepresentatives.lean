import Atlas.LinearGroups.Chevalley.TwistedE6.FixedSimpleRoots
import Atlas.LinearGroups.Chevalley.TwistedE6.FoldedReflectionGeometry
import Atlas.LinearGroups.Chevalley.WeightCompanionRootPermutation

/-! Actual graph–field-fixed normalizer words realizing the folded integral
root action. No order, full fixed-normalizer identification, or simplicity is
assumed. Root-label transport is distinct from root-parameter transport. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6
open Atlas.Comparisons.E6Lattice

theorem reflect_simpleRoot_coordinates (i : Fin 6) (x : Fin 6 → ℤ) :
    E6Data.reflect (E6Data.simpleRoot i) x = reflection i x := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [E6Data.reflect, E6Data.simpleRoot, E6Data.polar,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      Atlas.Comparisons.E6Lattice.norm, reflection, Pi.single_apply] <;> ring

variable (K : Type*) [Field K]

abbrev CompanionNormalizer :=
  weightCompanionExtendedWeylSubgroup (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K

def companionNormalizerRootAction : CompanionNormalizer K →* Equiv.Perm E6Data.Root :=
  weightCompanionNRootPermHom (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K

def latticeSimpleWeylInN (i : Fin 6) : CompanionNormalizer K :=
  weightCompanionSimpleWeylInN (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K
    ((rootDatum .E6).indexEquiv (E6Data.nodeEquiv i))

theorem latticeSimpleWeylInN_val (i : Fin 6) :
    (latticeSimpleWeylInN K i).val = simpleWeyl K (E6Data.nodeEquiv i) := rfl

theorem latticeSimpleWeylInN_rootAction (i : Fin 6) (β : E6Data.Root) :
    (companionNormalizerRootAction K (latticeSimpleWeylInN K i) β).val =
      reflection i β.val := by
  have hp : companionNormalizerRootAction K (latticeSimpleWeylInN K i) =
      E6Data.reflectionPerm (E6Data.baseIndexEquiv (E6Data.nodeEquiv i)).val :=
    weightCompanionNRootPermHom_simple (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) K
      ((rootDatum .E6).indexEquiv (E6Data.nodeEquiv i))
  rw [E6Data.baseIndexEquiv_apply, Equiv.symm_apply_apply] at hp
  rw [hp]
  exact reflect_simpleRoot_coordinates i β.val

def foldedWeylInN (i : Fin 4) : CompanionNormalizer K :=
  match i with
  | 0 => latticeSimpleWeylInN K 0 * latticeSimpleWeylInN K 4
  | 1 => latticeSimpleWeylInN K 1 * latticeSimpleWeylInN K 3
  | 2 => latticeSimpleWeylInN K 2
  | 3 => latticeSimpleWeylInN K 5

theorem foldedWeylInN_rootAction (i : Fin 4) (β : E6Data.Root) :
    (companionNormalizerRootAction K (foldedWeylInN K i) β).val =
      foldedReflectionLift ℤ i β.val := by
  fin_cases i <;>
    simp only [foldedWeylInN, map_mul, Equiv.Perm.mul_apply,
      latticeSimpleWeylInN_rootAction, foldedReflectionLift]

def foldedWeylWordInN (l : List (Fin 4)) : CompanionNormalizer K :=
  (l.map (foldedWeylInN K)).prod

theorem foldedWeylWordInN_rootAction (l : List (Fin 4)) (β : E6Data.Root) :
    (companionNormalizerRootAction K (foldedWeylWordInN K l) β).val =
      foldedRootWordAction l β.val := by
  induction l generalizing β with
  | nil =>
    simp only [foldedWeylWordInN, List.map_nil, List.prod_nil, map_one]
    rfl
  | cons i l ih =>
    change (companionNormalizerRootAction K
      (foldedWeylInN K i * foldedWeylWordInN K l) β).val = _
    rw [map_mul, Equiv.Perm.mul_apply, foldedWeylInN_rootAction, ih]
    rfl

theorem foldedWeylWordInN_representative (i : Fin 36) :
    (companionNormalizerRootAction K (foldedWeylWordInN K (foldedRootWord i))
      (E6Data.simpleRoot (foldedRootSeed i))).val = rootRepresentative i := by
  rw [foldedWeylWordInN_rootAction]
  exact foldedRootWord_representative i

variable (F : Type*) [Field F] [Finite F] [Finite K] [Algebra F K]

theorem foldedWeylInN_fixed (i : Fin 4) :
    (foldedWeylInN K i).val ∈ companionFixedSubgroup F K := by
  fin_cases i
  · change simpleWeyl K 0 * simpleWeyl K (simpleNode 0) ∈ _
    exact simpleWeyl_pair_fixed F K 0 (by decide)
  · change simpleWeyl K 2 * simpleWeyl K (simpleNode 2) ∈ _
    exact simpleWeyl_pair_fixed F K 2 (by decide)
  · change simpleWeyl K 3 ∈ _
    exact simpleWeyl_fixed F K 3 rfl
  · change simpleWeyl K 1 ∈ _
    exact simpleWeyl_fixed F K 1 rfl

theorem foldedWeylWordInN_fixed (l : List (Fin 4)) :
    (foldedWeylWordInN K l).val ∈ companionFixedSubgroup F K := by
  induction l with
  | nil => exact (companionFixedSubgroup F K).one_mem
  | cons i l ih =>
    exact (companionFixedSubgroup F K).mul_mem (foldedWeylInN_fixed K F i) ih

/-- Every positive integral root is reached by a literal fixed element of the
actual companion normalizer, starting from a simple root of the same orbit type. -/
theorem exists_fixed_normalizer_root_representative (i : Fin 36) :
    ∃ n : CompanionNormalizer K, n.val ∈ companionFixedSubgroup F K ∧
      (companionNormalizerRootAction K n (E6Data.simpleRoot (foldedRootSeed i))).val =
        rootRepresentative i :=
  ⟨foldedWeylWordInN K (foldedRootWord i),
    foldedWeylWordInN_fixed K F (foldedRootWord i), foldedWeylWordInN_representative K i⟩

end Atlas.Chevalley.TwistedE6

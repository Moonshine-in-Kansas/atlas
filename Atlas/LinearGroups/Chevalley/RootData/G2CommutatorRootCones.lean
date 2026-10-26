import Atlas.LinearGroups.Chevalley.RootData.G2LiteralRootLabels
import Atlas.LinearGroups.Chevalley.RootData.PositiveIntegralRootCone

/-! Source candidate: each output label in the complete literal G2 pair
table is a positive integral combination of that pair's two input labels.
The root pair is arbitrary; no ambient-simple-root or height-only replacement. -/

noncomputable section
namespace Atlas.Chevalley.RootData
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- All ten output occurrences in the five nontrivial commutators belong to
the positive integral cone on their own original pair. The ten commuting
pairs have no output roots and require no cone claim. -/
theorem g2_literal_commutator_root_cones (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -3) :
    let z := P.reflectionPerm j i
    let w := P.reflectionPerm i (P.reflectionPerm j i)
    let v := P.reflectionPerm i j
    let h := P.reflectionPerm j (P.reflectionPerm i j)
    PositiveIntegralRootCone P b i j z ∧ PositiveIntegralRootCone P b i j w ∧
    PositiveIntegralRootCone P b i j v ∧ PositiveIntegralRootCone P b i j h ∧
    PositiveIntegralRootCone P b i z w ∧ PositiveIntegralRootCone P b i z v ∧
    PositiveIntegralRootCone P b i z h ∧ PositiveIntegralRootCone P b i w v ∧
    PositiveIntegralRootCone P b j v h ∧ PositiveIntegralRootCone P b z w h := by
  let z := P.reflectionPerm j i
  let w := P.reflectionPerm i (P.reflectionPerm j i)
  let v := P.reflectionPerm i j
  let h := P.reflectionPerm j (P.reflectionPerm i j)
  have hl := g2_literal_root_labels P i j hij hji
  change P.root z = (1:ℤ) • P.root i + (1:ℤ) • P.root j ∧
    P.root w = (2:ℤ) • P.root i + (1:ℤ) • P.root j ∧
    P.root v = (3:ℤ) • P.root i + (1:ℤ) • P.root j ∧
    P.root h = (3:ℤ) • P.root i + (2:ℤ) • P.root j at hl
  obtain ⟨hz,hw,hv,hh⟩ := hl
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact positiveIntegralRootCone_of_root_eq P b i j z 1 1 (by decide) (by decide) hz
  · exact positiveIntegralRootCone_of_root_eq P b i j w 2 1 (by decide) (by decide) hw
  · exact positiveIntegralRootCone_of_root_eq P b i j v 3 1 (by decide) (by decide) hv
  · exact positiveIntegralRootCone_of_root_eq P b i j h 3 2 (by decide) (by decide) hh
  · apply positiveIntegralRootCone_of_root_eq P b i z w 1 1 (by decide) (by decide)
    rw [hw,hz]
    module
  · apply positiveIntegralRootCone_of_root_eq P b i z v 2 1 (by decide) (by decide)
    rw [hv,hz]
    module
  · apply positiveIntegralRootCone_of_root_eq P b i z h 1 2 (by decide) (by decide)
    rw [hh,hz]
    module
  · apply positiveIntegralRootCone_of_root_eq P b i w v 1 1 (by decide) (by decide)
    rw [hv,hw]
    module
  · apply positiveIntegralRootCone_of_root_eq P b j v h 1 1 (by decide) (by decide)
    rw [hh,hv]
    module
  · apply positiveIntegralRootCone_of_root_eq P b z w h 1 1 (by decide) (by decide)
    rw [hh,hz,hw]
    module

end Atlas.Chevalley.RootData

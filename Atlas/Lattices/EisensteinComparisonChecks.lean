import Atlas.Lattices.EisensteinComparisonSpace
import Atlas.Lattices.EisensteinPreimageData
import Atlas.Lattices.EisensteinGenerators
import Atlas.Codes.TernaryBinaryComparisonData
import Atlas.Lattices.LeechGeneratorCriterion

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra Matrix

def eisensteinComparisonSourceGenerator (j : Fin 20) : EisensteinCoordinates :=
  if h0 : j.val = 0 then eisensteinGlue
  else if h6 : j.val < 7 then eisensteinCodeGenerator ⟨j.val-1, by omega⟩
  else if h18 : j.val < 19 then eisensteinDifferenceGenerator ⟨j.val-7, by omega⟩
  else eisensteinAnchor

def eisensteinComparisonPhase (u : Fin 2) : Eisenstein :=
  if u=0 then 1 else eisensteinOmega

def eisensteinComparisonIntegerImage (z : EisensteinCoordinates) : IntegerCoordinates := fun p =>
  eisensteinIntegerPair (eisensteinCrossVector (eisensteinCrossIndex p)) z / 9

def eisensteinComparisonMask : Fin 20 → Fin 2 → ℕ :=
  ![![0, 478], ![3698, 0], ![200, 1684], ![200, 3217], ![3698, 2565], ![0, 1566], ![0, 0], ![0, 0], ![0, 64], ![0, 2629], ![0, 2565], ![20, 1456], ![20, 942], ![2998, 482], ![1292, 1846], ![1292, 1846], ![2998, 482], ![528, 1420], ![528, 1420], ![458, 936]]

theorem eisensteinComparison_forward_arithmetic : ∀ (j : Fin 20) (u : Fin 2),
    let z := eisensteinComparisonPhase u • eisensteinComparisonSourceGenerator j
    let x := eisensteinComparisonIntegerImage z
    let m := x ((0,0),0) % 2
    eisensteinComparisonMatrix *ᵥ eisensteinRealCoordinates (eisensteinCoordinateEmbedding z) =
      rationalEmbedding x ∧
    (m=0 ∨ m=1) ∧ (∀ p, x p % 2=m) ∧
    halfResidue x m = comparisonBinaryCoefficients (eisensteinComparisonMask j u) ∧
    (∑ p, x p) % 8 = 4*m := by
  decide +kernel

theorem eisensteinComparison_generator_check (j : Fin 20) (u : Fin 2) :
    ∃ x : IntegerCoordinates, x ∈ leech ∧
      eisensteinComparison (eisensteinCoordinateEmbedding
        (eisensteinComparisonPhase u • eisensteinComparisonSourceGenerator j)) =
        rationalEmbedding x := by
  obtain ⟨he, hm, hp, hc, hs⟩ := eisensteinComparison_forward_arithmetic j u
  refine ⟨_, (mem_leech _).mpr ⟨_, hm, hp, ?_, hs⟩, he⟩
  rw [hc]
  exact comparisonBinaryCoefficients_mem _

def eisensteinOldPoint (j : Fin 24) : Omega :=
  ((⟨j.val/8, by omega⟩, ⟨(j.val/4)%2, by omega⟩), ⟨j.val%4, by omega⟩)

def eisensteinComparisonTargetGenerator (j : Fin 38) : IntegerCoordinates :=
  if h24 : j.val < 24 then
    coordinateVector (eisensteinOldPoint ⟨j.val,h24⟩) 4 - coordinateVector ((0,0),0) 4
  else if h25 : j.val = 24 then coordinateVector ((0,0),0) 8
  else if h37 : j.val < 37 then
    (2 : ℤ) • golayIntegerLift (golayGenerators ⟨j.val-25, by omega⟩)
  else oddGlue ((0,0),0)

theorem eisensteinComparison_preimage_arithmetic : ∀ j : Fin 38,
    eisensteinComparisonMatrix *ᵥ eisensteinRealCoordinates
      (eisensteinCoordinateEmbedding (eisensteinLeechPreimage j)) =
    rationalEmbedding (eisensteinComparisonTargetGenerator j) := by
  decide +kernel

theorem eisensteinComparison_preimage_check (j : Fin 38) :
    eisensteinComparison (eisensteinCoordinateEmbedding (eisensteinLeechPreimage j)) =
      rationalEmbedding (eisensteinComparisonTargetGenerator j) :=
  eisensteinComparison_preimage_arithmetic j

end Atlas.Lattices

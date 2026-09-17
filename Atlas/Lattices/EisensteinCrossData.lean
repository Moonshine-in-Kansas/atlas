import Atlas.Lattices.EisensteinRational

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra

/-- A marked real cross in the Eisenstein congruence lattice. The marking
uses the retained binary-Golay coordinate order 8a+4b+c. -/
def eisensteinCrossVector : Fin 24 → EisensteinCoordinates :=
  ![![⟨1, 2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, -2⟩, ⟨4, 2⟩],
    ![⟨-1, -2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 2⟩, ⟨2, -2⟩],
    ![⟨-1, -2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -4⟩, ⟨2, 4⟩],
    ![⟨1, 2⟩, ⟨-1, -2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-1, -2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-1, -2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -4⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 4⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-3, 0⟩, ⟨3, 0⟩, ⟨3, 0⟩, ⟨-3, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-3, 0⟩, ⟨3, 0⟩, ⟨-3, 0⟩, ⟨3, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -4⟩, ⟨2, 4⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-2, -2⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨-2, -2⟩, ⟨-2, -2⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-2, -2⟩],
    ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨-2, 2⟩, ⟨4, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 2⟩, ⟨-4, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨2, 2⟩, ⟨2, 2⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 2⟩, ⟨0, -2⟩, ⟨0, -2⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -2⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, 2⟩],
    ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨2, 4⟩, ⟨2, 4⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 2⟩, ⟨0, -2⟩, ⟨2, 2⟩, ⟨0, -2⟩, ⟨0, -2⟩, ⟨2, 2⟩, ⟨-2, 0⟩, ⟨-2, 0⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩],
    ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-4, -2⟩, ⟨2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 2⟩, ⟨2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -2⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨-2, -2⟩, ⟨-2, -2⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 2⟩],
    ![⟨-3, 0⟩, ⟨-3, 0⟩, ⟨3, 0⟩, ⟨3, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨2, 2⟩, ⟨0, -2⟩, ⟨2, 2⟩, ⟨2, 2⟩, ⟨0, -2⟩, ⟨-2, 0⟩, ⟨-2, 0⟩]]

def eisensteinCrossLift (j : Fin 24) : ℤ :=
  ((eisensteinCrossVector j 0).re + (eisensteinCrossVector j 0).im) % 3

def eisensteinCrossWitness (j : Fin 24) : EisensteinCoordinates := fun i =>
  let r := (eisensteinCrossVector j i).re - eisensteinCrossLift j
  let s := (eisensteinCrossVector j i).im
  ⟨(-r + 2*s)/3, (-2*r+s)/3⟩

def eisensteinCrossSumWitness (j : Fin 24) : Eisenstein :=
  let z := (∑ i, eisensteinCrossVector j i) + 3 * (eisensteinCrossLift j : Eisenstein)
  ⟨(-z.re + 2*z.im)/9, (-2*z.re+z.im)/9⟩

theorem eisensteinCross_congruence_check : ∀ j : Fin 24,
    (∀ i, eisensteinCrossVector j i = (eisensteinCrossLift j : Eisenstein) +
      eisensteinTheta * eisensteinCrossWitness j i) ∧
    eisensteinWordResidue (eisensteinCrossWitness j) =
      ternaryEncoder (ternaryDecoder (eisensteinWordResidue (eisensteinCrossWitness j))) ∧
    (∑ i, eisensteinCrossVector j i) + 3 * (eisensteinCrossLift j : Eisenstein) =
      (3 * eisensteinTheta) * eisensteinCrossSumWitness j := by
  decide +kernel

theorem eisensteinCross_mem (j : Fin 24) :
    eisensteinCrossVector j ∈ eisensteinLeechModule := by
  obtain ⟨hc, ht, hs⟩ := eisensteinCross_congruence_check j
  refine ⟨(eisensteinCrossLift j : Eisenstein), eisensteinCrossWitness j, hc, ?_,
    ⟨eisensteinCrossSumWitness j, hs⟩⟩
  rw [ht]
  exact ⟨_, rfl⟩

/-- Twice the unscaled real pairing, retained over integers for the local Gram check. -/
def eisensteinIntegerPair (z w : EisensteinCoordinates) : ℤ :=
  ∑ i, (2*(z i).re*(w i).re - (z i).re*(w i).im -
    (z i).im*(w i).re + 2*(z i).im*(w i).im)

theorem eisensteinCross_gram_check : ∀ i j : Fin 24,
    eisensteinIntegerPair (eisensteinCrossVector i) (eisensteinCrossVector j) =
      if i = j then 72 else 0 := by
  decide +kernel

end Atlas.Lattices

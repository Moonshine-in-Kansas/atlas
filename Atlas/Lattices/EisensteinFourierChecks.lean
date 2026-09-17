import Atlas.Lattices.EisensteinFourierMatrix
import Atlas.Lattices.EisensteinComparisonChecks

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra Matrix

def eisensteinFourierDirection (d : Fin 2) : Matrix (Fin 12) (Fin 12) EisensteinRational :=
  if d=0 then eisensteinFourierMatrix else eisensteinFourierMatrix.conjTranspose

def eisensteinFourierIntegerDirection (d : Fin 2) : Matrix (Fin 12) (Fin 12) Eisenstein :=
  if d=0 then eisensteinFourierNumerator else eisensteinFourierNumerator.conjTranspose

def eisensteinFourierIntegerImage (d : Fin 2) (z : EisensteinCoordinates) :
    EisensteinCoordinates := fun i =>
  let w := (eisensteinFourierIntegerDirection d) *ᵥ z
  ⟨(w i).re/3, (w i).im/3⟩

def eisensteinFourierLift (z : EisensteinCoordinates) : ℤ := ((z 0).re+(z 0).im)%3

def eisensteinFourierWitness (z : EisensteinCoordinates) : EisensteinCoordinates := fun i =>
  let r := (z i).re-eisensteinFourierLift z
  let s := (z i).im
  ⟨(-r+2*s)/3,(-2*r+s)/3⟩

def eisensteinFourierSumWitness (z : EisensteinCoordinates) : Eisenstein :=
  let w := (∑ i,z i)+3*(eisensteinFourierLift z : Eisenstein)
  ⟨(-w.re+2*w.im)/9,(-2*w.re+w.im)/9⟩

set_option maxHeartbeats 0 in
-- This bounded check covers both directions on forty integral generators.
theorem eisensteinFourier_generator_arithmetic : ∀ (d : Fin 2) (j : Fin 20) (p : Fin 2),
    let z := eisensteinComparisonPhase p • eisensteinComparisonSourceGenerator j
    let w := eisensteinFourierIntegerImage d z
    eisensteinFourierDirection d *ᵥ eisensteinCoordinateEmbedding z =
      eisensteinCoordinateEmbedding w ∧
    (∀ i,w i=(eisensteinFourierLift w : Eisenstein)+
      eisensteinTheta*eisensteinFourierWitness w i) ∧
    eisensteinWordResidue (eisensteinFourierWitness w) =
      ternaryEncoder (ternaryDecoder (eisensteinWordResidue (eisensteinFourierWitness w))) ∧
    (∑ i,w i)+3*(eisensteinFourierLift w : Eisenstein) =
      (3*eisensteinTheta)*eisensteinFourierSumWitness w := by
  decide +kernel

theorem eisensteinFourier_generator_mem (d : Fin 2) (j : Fin 20) (p : Fin 2) :
    eisensteinFourierDirection d *ᵥ eisensteinCoordinateEmbedding
      (eisensteinComparisonPhase p • eisensteinComparisonSourceGenerator j) ∈
      rationalEisensteinLattice := by
  obtain ⟨he, hc, ht, hs⟩ := eisensteinFourier_generator_arithmetic d j p
  rw [he]
  refine Submodule.mem_map.mpr ⟨_, ?_, rfl⟩
  refine ⟨_, _, hc, ?_, ⟨_, hs⟩⟩
  rw [ht]
  exact ⟨_, rfl⟩

end Atlas.Lattices

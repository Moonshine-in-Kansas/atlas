import Atlas.Algebra.Eisenstein
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.Pi

namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators

/-- Coordinate differences and the theta-multiple of one coordinate generate
all triples whose coordinate sum is divisible by theta. -/
theorem eisenstein_three_mem_of_sum_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι] (o : ι)
    (S : Submodule Eisenstein (ι → Eisenstein))
    (hS : ∀ i, (3 : Eisenstein) • (Pi.single i 1 - Pi.single o 1) ∈ S)
    (hθ : (3 * eisensteinTheta) • Pi.single o 1 ∈ S)
    (a : ι → Eisenstein) (ha : eisensteinTheta ∣ ∑ i, a i) :
    (3 : Eisenstein) • a ∈ S := by
  obtain ⟨b, hb⟩ := ha
  have hsum : ∑ i, a i • ((3 : Eisenstein) • (Pi.single i 1 - Pi.single o 1)) ∈ S :=
    S.sum_mem fun i _ => S.smul_mem (a i) (hS i)
  have hanchor : b • ((3 * eisensteinTheta) • Pi.single o 1) ∈ S := S.smul_mem b hθ
  have he : (3 : Eisenstein) • a =
      (∑ i, a i • ((3 : Eisenstein) • (Pi.single i 1 - Pi.single o 1))) +
        b • ((3 * eisensteinTheta) • Pi.single o 1) := by
    funext j
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      mul_sub, Finset.sum_sub_distrib]
    simp only [mul_left_comm (a _) 3, ← Finset.mul_sum]
    have hs : ∑ i, a i * (Pi.single i 1 : ι → Eisenstein) j = a j := by
      simp [Pi.single_apply, mul_ite]
    rw [hs]
    rw [← Finset.sum_mul, hb]
    ring
  rw [he]
  exact S.add_mem hsum hanchor

end Atlas.Lattices

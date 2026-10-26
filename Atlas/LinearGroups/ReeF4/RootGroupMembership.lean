import Atlas.LinearGroups.ReeF4.RootGroupTorusConjugation
import Atlas.LinearGroups.ReeF4.RootGroupSubgroup
import Atlas.LinearGroups.ReeF4.RootGroupUnits
import Atlas.LinearGroups.ReeF4.IntrinsicGroup
import Atlas.LinearGroups.ReeF4.ShortRootMembership
import Atlas.LinearGroups.ReeF4.TorusStarCompatibility

/-! The actual two-parameter short root subgroup lies in the full intrinsic
polynomial-and-partial-product stabilizer. Its central parameters are obtained
from squares, using the bijective Tits norm on nonzero field elements. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem shortRootEquiv_mem_modelSubgroup (m : ℕ) :
    (shortRootEquiv : TraceZero F ≃ₗ[F] TraceZero F) ∈ modelSubgroup F m := by
  rw [mem_modelSubgroup_iff]
  exact ⟨shortRootEquiv_mem_polynomialStabilizer,
    shortRoot_mem_candidatePartialStabilizer (thetaInv F m).toRingHom⟩

theorem torusEquiv_mem_modelSubgroup {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b : Fˣ) :
    torusEquiv m a b ∈ modelSubgroup F m := by
  rw [mem_modelSubgroup_iff]
  exact ⟨torusEquiv_mem_polynomialStabilizer m a b,
    torus_mem_candidatePartialStabilizer hcard a b⟩

theorem shortRootPairEquiv_parameter_mem {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a : F) :
    shortRootPairEquiv m hcard a 0 ∈ modelSubgroup F m := by
  by_cases ha : a = 0
  · subst a
    rw [shortRootPairEquiv_zero]
    exact (modelSubgroup F m).one_mem
  · let u : Fˣ := Units.mk0 a ha
    change shortRootPairEquiv m hcard (u : F) 0 ∈ modelSubgroup F m
    rw [shortRootPairEquiv_unit_zero hcard]
    exact (modelSubgroup F m).mul_mem
      ((modelSubgroup F m).mul_mem (torusEquiv_mem_modelSubgroup hcard _ _)
        (shortRootEquiv_mem_modelSubgroup m)) (torusEquiv_mem_modelSubgroup hcard _ _)

theorem shortRootPairEquiv_center_mem {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (b : F) :
    shortRootPairEquiv m hcard 0 b ∈ modelSubgroup F m := by
  by_cases hb : b = 0
  · subst b
    rw [shortRootPairEquiv_zero]
    exact (modelSubgroup F m).one_mem
  · let v : Fˣ := Units.mk0 b hb
    obtain ⟨u, hu⟩ := (thetaNormEquiv hcard).surjective v
    have hn : theta F m (u : F) * (u : F) = b := by
      have h := congrArg (fun z : Fˣ => (z : F)) hu
      change (u : F) * theta F m (u : F) = b at h
      simpa only [mul_comm] using h
    have hmem := (modelSubgroup F m).mul_mem
      (shortRootPairEquiv_parameter_mem hcard (u : F))
      (shortRootPairEquiv_parameter_mem hcard (u : F))
    rw [shortRootPairEquiv_mul] at hmem
    simpa only [CharTwo.add_self_eq_zero, zero_add, hn] using hmem

theorem shortRootPairEquiv_mem_modelSubgroup {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b : F) :
    shortRootPairEquiv m hcard a b ∈ modelSubgroup F m := by
  have hmem := (modelSubgroup F m).mul_mem
    (shortRootPairEquiv_parameter_mem hcard a) (shortRootPairEquiv_center_mem hcard b)
  rw [shortRootPairEquiv_mul] at hmem
  simpa only [add_zero, zero_add, mul_zero] using hmem

theorem shortRootSubgroup_le_modelSubgroup {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    shortRootSubgroup m hcard ≤ modelSubgroup F m := by
  rintro g ⟨⟨a,b⟩,rfl⟩
  exact shortRootPairEquiv_mem_modelSubgroup hcard a b

end Atlas.ReeF4

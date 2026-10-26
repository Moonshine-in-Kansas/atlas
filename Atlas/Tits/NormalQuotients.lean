import Atlas.Tits.LocalGeneration
import Atlas.GroupTheory.PrimitivePerfectFrameSimplicity

namespace Atlas.Tits

/-- Every nontrivial normal subgroup is transitive on the actual orthogonal shell. -/
theorem normal_neighbours_transitive (N : Subgroup Ambient) [N.Normal] (hN : N ≠ ⊥) :
    MulAction.IsPretransitive N Neighbours := by
  letI := neighboursPrimitive
  exact Atlas.GroupTheory.normal_pretransitive N hN

/-- The quotient is an image of the actual pair stabilizer, hence its order divides 20480. -/
theorem normal_quotient_card_dvd (N : Subgroup Ambient) [N.Normal] (hN : N ≠ ⊥) :
    Nat.card (Ambient ⧸ N) ∣ 20480 := by
  letI := neighboursPrimitive
  have h := Atlas.GroupTheory.normal_quotient_card_dvd_stabilizer N hN referenceNeighbour
  exact cardPairStabilizer ▸ h

/-- Elements whose cube is one vanish in every nontrivial normal quotient. -/
theorem cube_eq_one_mem_normal (N : Subgroup Ambient) [N.Normal] (hN : N ≠ ⊥)
    (g : Ambient) (hg : g ^ 3 = 1) : g ∈ N := by
  let f := QuotientGroup.mk' N
  have hc : (f g) ^ 3 = 1 := by rw [← map_pow, hg, map_one]
  have ho : orderOf (f g) ∣ 3 := orderOf_dvd_of_pow_eq_one hc
  have hd : orderOf (f g) ∣ 20480 :=
    (orderOf_dvd_natCard (f g)).trans (normal_quotient_card_dvd N hN)
  have hi : orderOf (f g) = 1 := by
    have h := Nat.dvd_gcd ho hd
    norm_num at h
    exact orderOf_eq_one_iff.mpr h
  exact (QuotientGroup.eq_one_iff g).mp (orderOf_eq_one_iff.mp hi)

end Atlas.Tits

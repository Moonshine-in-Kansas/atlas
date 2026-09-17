import Atlas.Fischer.CocodeCoordinates
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Lattice

namespace Atlas.Fischer
open Atlas.Codes

noncomputable def cocodeInvolution (i : Omega) : Multiplicative Cocode :=
  Multiplicative.ofAdd (coordinateCocode i)

theorem cocodeInvolution_square (i : Omega) : cocodeInvolution i ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [pow_two]
  change coordinateCocode i + coordinateCocode i = 0
  rw [← two_smul Bit, show (2 : Bit) = 0 from rfl, zero_smul]

theorem cocodeInvolution_ne_one (i : Omega) : cocodeInvolution i ≠ 1 := by
  intro h
  have hc : coordinateCocode i = 0 := congrArg Multiplicative.toAdd h
  have hp := coordinateCocode_parity i
  rw [hc, map_zero] at hp
  exact zero_ne_one hp

theorem cocodeInvolution_order (i : Omega) : orderOf (cocodeInvolution i) = 2 := by
  exact orderOf_eq_prime (cocodeInvolution_square i) (cocodeInvolution_ne_one i)

theorem cocodeInvolutions_relation (S : Finset Omega) :
    (∏ i ∈ S, cocodeInvolution i) = 1 ↔ binarySupportEquiv.symm S ∈ golay := by
  change (∏ i ∈ S, Multiplicative.ofAdd (coordinateCocode i)) = 1 ↔ _
  rw [← ofAdd_sum]
  exact coordinateCocode_sum_eq_zero S

theorem cocodeInvolutions_generate : Subgroup.closure (Set.range cocodeInvolution) = ⊤ := by
  apply top_unique
  intro d _
  obtain ⟨S, hS⟩ := coordinateCocode_representation d.toAdd
  have hd : d = Multiplicative.ofAdd (∑ i ∈ S, coordinateCocode i) :=
    congrArg Multiplicative.ofAdd hS
  rw [hd, ofAdd_sum]
  exact Subgroup.prod_mem _ (fun i _ => Subgroup.subset_closure ⟨i, rfl⟩)

end Atlas.Fischer

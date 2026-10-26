import Atlas.Tits.FiveQuartetMultiplierProperties
import Mathlib.GroupTheory.Transfer

/-! Transfer from the actual pair stabilizer. The quotient used below is the
 left coset space, with no normality assertion about the pair stabilizer. -/
namespace Atlas.Tits

/-- The actual transfer of the geometric five-quartet multiplier. -/
noncomputable def transfer : Ambient →* (ZMod 5)ˣ :=
  fiveQuartetMultiplier.transfer

/-- Left cosets of the pair stabilizer identify equivariantly with the actual
 1755 neighbours of the distinguished cross. -/
noncomputable def neighbourCosetEquiv : (Ambient ⧸ pairStabilizer) ≃ Neighbours :=
  Equiv.ofBijective (MulAction.ofQuotientStabilizer Ambient referenceNeighbour)
    ⟨MulAction.injective_ofQuotientStabilizer Ambient referenceNeighbour, by
      intro v
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Ambient referenceNeighbour v
      exact ⟨QuotientGroup.mk g,hg⟩⟩

@[simp] theorem neighbourCosetEquiv_mk (g : Ambient) :
    neighbourCosetEquiv (QuotientGroup.mk g) = g • referenceNeighbour := rfl

@[simp] theorem neighbourCosetEquiv_smul (g : Ambient) (q : Ambient ⧸ pairStabilizer) :
    neighbourCosetEquiv (g • q) = g • neighbourCosetEquiv q :=
  MulAction.ofQuotientStabilizer_smul Ambient referenceNeighbour g q

theorem neighbourCosetEquiv_period (g : Ambient) (q : Ambient ⧸ pairStabilizer) :
    Function.minimalPeriod (g • ·) q =
      Function.minimalPeriod (g • ·) (neighbourCosetEquiv q) := by
  apply Nat.dvd_antisymm
  · apply (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mp
    apply neighbourCosetEquiv.injective
    rw [neighbourCosetEquiv_smul]
    exact (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mpr (dvd_refl _)
  · apply (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mp
    rw [← neighbourCosetEquiv_smul]
    congr 1
    exact (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mpr (dvd_refl _)

/-- Cycle-product formula on the actual left cosets, using the pinned mathlib
 transfer. Each factor is the multiplier of the transported cycle power. -/
theorem transfer_cycle_product (g : Ambient)
    [Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g)
      (Ambient ⧸ pairStabilizer)))] :
    transfer g =
      ∏ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g)
        (Ambient ⧸ pairStabilizer)),
      fiveQuartetMultiplier
        ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem pairStabilizer g q.out⟩ :=
  MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot fiveQuartetMultiplier g

/-- The cycle lengths in the transfer are exactly the lengths in the geometric
 neighbour action, rather than those of an unrelated permutation model. -/
theorem transfer_cycle_product_neighbour_period (g : Ambient)
    [Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g)
      (Ambient ⧸ pairStabilizer)))] :
    transfer g =
      ∏ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g)
        (Ambient ⧸ pairStabilizer)),
      fiveQuartetMultiplier
        ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) (neighbourCosetEquiv q.out) * q.out.out,
          by rw [← neighbourCosetEquiv_period];
             exact QuotientGroup.out_conj_pow_minimalPeriod_mem pairStabilizer g q.out⟩ := by
  simpa only [neighbourCosetEquiv_period] using transfer_cycle_product g

end Atlas.Tits

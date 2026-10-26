import Atlas.Tits.TransferLocalCharacters

namespace Atlas.Tits
open Atlas.GroupTheory
open scoped BigOperators

abbrev GeometricCycles (g : Ambient) :=
  MulAction.orbitRel.Quotient (Subgroup.zpowers g) Neighbours

noncomputable instance geometricCyclesFintype (g : Ambient) : Fintype (GeometricCycles g) :=
  Fintype.ofFinite _

noncomputable def pointCycleValue (g : Ambient) (v : Neighbours) : (ZMod 5)ˣ :=
  multiplierAt v ⟨g ^ Function.minimalPeriod (g • ·) v,
    MulAction.pow_smul_eq_iff_minimalPeriod_dvd.mpr (dvd_refl _)⟩

theorem neighbour_period_same_orbit (g : Ambient) (v w : Neighbours)
    (h : MulAction.orbitRel (Subgroup.zpowers g) Neighbours v w) :
    Function.minimalPeriod (g • ·) v = Function.minimalPeriod (g • ·) w := by
  rw [←card_zpowers_orbit_eq_minimalPeriod,←card_zpowers_orbit_eq_minimalPeriod]
  exact Nat.card_congr (Equiv.setCongr (MulAction.orbit_eq_iff.mpr h))

theorem pointCycleValue_orbit (g : Ambient) (v w : Neighbours)
    (h : MulAction.orbitRel (Subgroup.zpowers g) Neighbours v w) :
    pointCycleValue g v = pointCycleValue g w := by
  obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp h
  have hp := neighbour_period_same_orbit g v w h
  have hc : Commute k.val g := by
    obtain ⟨n,hn⟩ := k.prop
    rw [←hn]
    exact Commute.zpow_self _ _
  unfold pointCycleValue
  simp only [hp]
  symm
  exact multiplierAt_centralizing_transport w v _ k.val _ _
    (hc.pow_right _) hk

/-- Each factor is a local character of the actual power closing that cycle. -/
noncomputable def geometricCycleValue (g : Ambient) : GeometricCycles g → (ZMod 5)ˣ :=
  Quotient.lift (pointCycleValue g) (pointCycleValue_orbit g)

@[simp] theorem geometricCycleValue_mk (g : Ambient) (v : Neighbours) :
    geometricCycleValue g (Quotient.mk _ v) = pointCycleValue g v := rfl

theorem geometricCycleValue_out (g : Ambient) (O : GeometricCycles g) :
    geometricCycleValue g O = pointCycleValue g O.out := by
  exact (congrArg (geometricCycleValue g) (Quotient.out_eq O)).symm

noncomputable def neighbourCycleEquiv (g : Ambient) :
    MulAction.orbitRel.Quotient (Subgroup.zpowers g) (Ambient ⧸ pairStabilizer) ≃
      GeometricCycles g :=
  Quotient.congr neighbourCosetEquiv (by
    intro a b
    constructor
    · intro h
      obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp h
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨k,?_⟩
      change k.val • neighbourCosetEquiv b = neighbourCosetEquiv a
      rw [←neighbourCosetEquiv_smul]
      exact congrArg neighbourCosetEquiv hk
    · intro h
      obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp h
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨k,?_⟩
      apply neighbourCosetEquiv.injective
      change neighbourCosetEquiv (k.val • b) = neighbourCosetEquiv a
      rw [neighbourCosetEquiv_smul]
      exact hk)

theorem neighbourCosetEquiv_out (q : Ambient ⧸ pairStabilizer) :
    q.out • referenceNeighbour = neighbourCosetEquiv q := by
  exact congrArg neighbourCosetEquiv (Quotient.out_eq q)

/-- The transfer is a product over the cycles of the actual geometric action. -/
theorem transfer_geometric_cycle_product (g : Ambient) :
    transfer g = ∏ O : GeometricCycles g, geometricCycleValue g O := by
  classical
  letI := Fintype.ofFinite
    (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (Ambient ⧸ pairStabilizer))
  rw [transfer_cycle_product_neighbour_period]
  apply Fintype.prod_equiv (neighbourCycleEquiv g)
  intro O
  have he : neighbourCycleEquiv g O = Quotient.mk _ (neighbourCosetEquiv O.out) := by
    conv_lhs => rw [←Quotient.out_eq' O]
    rfl
  rw [he,geometricCycleValue_mk]
  unfold pointCycleValue
  rw [multiplierAt_eq_transport _ O.out.out (neighbourCosetEquiv_out O.out)]
  rfl

end Atlas.Tits

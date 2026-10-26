import Atlas.Tits.TransferRowCycles

/-! Global alpha cycles in an external coordinate row. The row counts refer to
actual orbits on the full neighbour shell, rather than independent row actions. -/

namespace Atlas.Tits
open Atlas.Rudvalis

abbrev AlphaCycles := MulAction.orbitRel.Quotient (Subgroup.zpowers localAlpha) Neighbours

noncomputable def AlphaCycleInRow (p : Point) (O : AlphaCycles) : Prop :=
  O.out.val ∈ coordinateRowFrame p

theorem alpha_powers_row_mem (p : Point) (g : Subgroup.zpowers localAlpha)
    (c : Neighbours) (hc : c.val ∈ coordinateRowFrame p) :
    (g • c).val ∈ coordinateRowFrame p := by
  obtain ⟨n,hn⟩ := show g.val ∈ Submonoid.powers localAlpha from
    mem_powers_iff_mem_zpowers.mpr g.prop
  change (g.val • c).val ∈ coordinateRowFrame p
  rw [← hn]
  change (localAlpha ^ n • c).val ∈ coordinateRowFrame p
  clear hn
  induction n with
  | zero => simpa using hc
  | succ n ih =>
    rw [pow_succ',mul_smul]
    exact localAlpha_row_mem p _ ih

theorem alpha_orbit_row_iff (p : Point) (O : AlphaCycles) (c : O.orbit) :
    c.val.val ∈ coordinateRowFrame p ↔ AlphaCycleInRow p O := by
  have hc : c.val ∈ MulAction.orbit (Subgroup.zpowers localAlpha) O.out := by
    simpa only [MulAction.orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq'] using c.prop
  obtain ⟨g,hg⟩ := hc
  constructor
  · intro h
    have hh := alpha_powers_row_mem p g⁻¹ c.val h
    rw [← hg,inv_smul_smul] at hh
    exact hh
  · intro h
    rw [← hg]
    exact alpha_powers_row_mem p g O.out h

noncomputable def coordinateRowEquivGlobalCycles (p : Point) :
    CoordinateRowNeighbours p ≃ Σ O : {O : AlphaCycles // AlphaCycleInRow p O}, O.val.orbit :=
  (Equiv.subtypeEquiv (MulAction.selfEquivSigmaOrbits' (Subgroup.zpowers localAlpha) Neighbours)
    (fun c => alpha_orbit_row_iff p
      ((MulAction.selfEquivSigmaOrbits' (Subgroup.zpowers localAlpha) Neighbours) c).fst
      ((MulAction.selfEquivSigmaOrbits' (Subgroup.zpowers localAlpha) Neighbours) c).snd)).trans
    (Equiv.subtypeSigmaEquiv (fun O : AlphaCycles => O.orbit) (AlphaCycleInRow p))

theorem alphaCycle_row_card (p : Point) (hp : p ≠ rowLabel 0)
    (O : AlphaCycles) (hO : AlphaCycleInRow p O) : Nat.card O.orbit = 2 := by
  rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq',
    Atlas.GroupTheory.card_zpowers_orbit_eq_minimalPeriod]
  apply (localAlpha_period_two_iff O.out).mpr
  constructor
  · exact (localAlpha_square_fixed_iff O.out).mpr (coordinateRowFrame_subset p hO)
  · intro hf
    obtain ⟨x,hx⟩ := hO
    obtain ⟨y,hy⟩ := (localAlpha_fixed_iff O.out).mp hf
    exact hp (coordinateCross_row_of_eq (hx.trans hy.symm))

theorem alpha_global_cycles_in_row_card (p : Point) (hp : p ≠ rowLabel 0) :
    Nat.card {O : AlphaCycles // AlphaCycleInRow p O} = 2 := by
  classical
  letI := Fintype.ofFinite {O : AlphaCycles // AlphaCycleInRow p O}
  have hc := coordinateRowNeighbours_card p hp
  rw [Nat.card_congr (coordinateRowEquivGlobalCycles p),Nat.card_sigma] at hc
  have hval (O : {O : AlphaCycles // AlphaCycleInRow p O}) : Nat.card O.val.orbit = 2 :=
    alphaCycle_row_card p hp O.val O.prop
  simp only [hval,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    ← Nat.card_eq_fintype_card] at hc
  omega

/-- Each global two-cycle lies in exactly one of the six external rows. -/
theorem alpha_two_cycle_unique_row (O : AlphaCycles) (hO : Nat.card O.orbit = 2) :
    ∃! p : {p : Point // p ≠ rowLabel 0}, AlphaCycleInRow p.val O := by
  have hper : Function.minimalPeriod (localAlpha • ·) O.out = 2 := by
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq',
      Atlas.GroupTheory.card_zpowers_orbit_eq_minimalPeriod] at hO
    exact hO
  obtain ⟨hs,hn⟩ := (localAlpha_period_two_iff O.out).mp hper
  obtain ⟨⟨p,x⟩,hx⟩ := coordinateFrame_rep O.out.val
    ((localAlpha_square_fixed_iff O.out).mp hs)
  have hp : p ≠ rowLabel 0 := by
    intro he
    apply hn
    apply (localAlpha_fixed_iff O.out).mpr
    exact ⟨x,by simpa only [he] using hx⟩
  refine ⟨⟨p,hp⟩,⟨x,hx⟩,?_⟩
  rintro q ⟨y,hy⟩
  apply Subtype.ext
  exact coordinateCross_row_of_eq (hy.trans hx.symm)

end Atlas.Tits

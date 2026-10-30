import Atlas.Sporadic.Janko1.WhitelawSNormalizer

/-!
Uncompiled source-only successor. Nine explicit seven-coordinate equalities
connect the ten existing H-orbits inside the actual generated-group orbit.
The witnesses are checked directly, without searching a group or orbit table.
This proves W is contained in G.w0; it does not assert S-invariance of W.
-/
noncomputable section
namespace Atlas.Janko1

/-- An unsquared equality, including the sign and projective scalar. -/
abbrev WhitelawSTransport (r s : Fin 10) (a b : SignParameters)
    (i : Fin 7) (j : Fin 3) (c : Field) : Prop :=
  c • sCoordinateAction (signedWhitelawSeed r a) =
    hCoordinateAction (b, i, j) (whitelawSeed s)

set_option maxRecDepth 8192 in
theorem whitelaw_S_link_0_3 :
    WhitelawSTransport 0 3 0 ![0,1,1] 4 1 2 := by
  funext k
  fin_cases k <;> decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_link_0_4 :
    WhitelawSTransport 0 4 ![0,1,0] ![1,1,1] 6 0 1 := by
  funext k
  fin_cases k <;> decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_link_0_5 :
    WhitelawSTransport 0 5 ![1,0,0] ![0,0,1] 1 2 3 := by
  funext k
  fin_cases k <;> decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_link_0_6 :
    WhitelawSTransport 0 6 ![1,1,0] ![1,0,0] 2 0 (-3) := by
  funext k
  fin_cases k <;> decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_link_3_1 :
    WhitelawSTransport 3 1 ![0,0,1] ![1,1,1] 3 0 1 := by
  funext k
  fin_cases k <;> decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_link_3_2 :
    WhitelawSTransport 3 2 0 ![0,0,1] 3 2 (-4) := by
  funext k
  fin_cases k <;> decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_link_3_7 :
    WhitelawSTransport 3 7 ![1,0,1] 0 0 0 4 := by
  funext k
  fin_cases k <;> decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_link_3_8 :
    WhitelawSTransport 3 8 ![1,0,0] ![0,0,1] 0 2 5 := by
  funext k
  fin_cases k <;> decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_link_3_9 :
    WhitelawSTransport 3 9 ![0,1,1] ![0,1,0] 5 1 4 := by
  funext k
  fin_cases k <;> decide

/-- Transport is by a literal product of the installed automorphisms. -/
theorem whitelawSTransport_seed_mem_orbit {r s : Fin 10} {a b : SignParameters}
    {i : Fin 7} {j : Fin 3} {c : Field}
    (ht : WhitelawSTransport r s a b i j c) :
    whitelawSeedPoint s ∈ MulAction.orbit Model (whitelawSeedPoint r) := by
  have hp : (hNormalFormEquiv (b, i, j) : G2.Model Field) • whitelawSeedPoint s =
      S • (signElement a • whitelawSeedPoint r) := by
    change (hNormalFormEquiv (b, i, j) : G2.Model Field) •
      coordinatePoint (whitelawSeed s) (whitelawSeed_ne_zero s) =
        S • (signElement a • coordinatePoint (whitelawSeed r) (whitelawSeed_ne_zero r))
    simp only [coordinatePoint_smul]
    rw [coordinatePoint_eq_iff]
    refine ⟨c, ?_⟩
    rw [imaginaryCoordinateAction_normalForm, imaginaryCoordinateAction_S,
      imaginaryCoordinateAction_sign]
    exact ht
  let g : Model :=
    ⟨(hNormalFormEquiv (b, i, j) : G2.Model Field)⁻¹ * (S * signElement a),
      generated.mul_mem
        (generated.inv_mem (H_le_generated (hNormalFormEquiv (b, i, j)).property))
        (generated.mul_mem S_mem
          (signSubgroup_le_generated (signElement_mem_signSubgroup a)))⟩
  refine ⟨g, ?_⟩
  change ((hNormalFormEquiv (b, i, j) : G2.Model Field)⁻¹ *
    (S * signElement a)) • whitelawSeedPoint r = whitelawSeedPoint s
  rw [mul_smul, mul_smul, ← hp, inv_smul_smul]

/-- The nine links form a tree rooted at seed 0, with an intermediate vertex 3. -/
theorem whitelawSeed_generatedOrbit_eq_zero (r : Fin 10) :
    MulAction.orbit Model (whitelawSeedPoint r) =
      MulAction.orbit Model (whitelawSeedPoint 0) := by
  have h3 : MulAction.orbit Model (whitelawSeedPoint 3) =
      MulAction.orbit Model (whitelawSeedPoint 0) :=
    MulAction.orbit_eq_iff.mpr (whitelawSTransport_seed_mem_orbit whitelaw_S_link_0_3)
  fin_cases r
  · rfl
  · exact (MulAction.orbit_eq_iff.mpr
      (whitelawSTransport_seed_mem_orbit whitelaw_S_link_3_1)).trans h3
  · exact (MulAction.orbit_eq_iff.mpr
      (whitelawSTransport_seed_mem_orbit whitelaw_S_link_3_2)).trans h3
  · exact h3
  · exact MulAction.orbit_eq_iff.mpr (whitelawSTransport_seed_mem_orbit whitelaw_S_link_0_4)
  · exact MulAction.orbit_eq_iff.mpr (whitelawSTransport_seed_mem_orbit whitelaw_S_link_0_5)
  · exact MulAction.orbit_eq_iff.mpr (whitelawSTransport_seed_mem_orbit whitelaw_S_link_0_6)
  · exact (MulAction.orbit_eq_iff.mpr
      (whitelawSTransport_seed_mem_orbit whitelaw_S_link_3_7)).trans h3
  · exact (MulAction.orbit_eq_iff.mpr
      (whitelawSTransport_seed_mem_orbit whitelaw_S_link_3_8)).trans h3
  · exact (MulAction.orbit_eq_iff.mpr
      (whitelawSTransport_seed_mem_orbit whitelaw_S_link_3_9)).trans h3

set_option maxRecDepth 8192 in
theorem whitelawVector_seed_two_coordinates :
    (-1 : Field) • whitelawVector =
      hCoordinateAction (![1,0,1], (1 : Fin 7), (1 : Fin 3)) (whitelawSeed 2) := by
  funext k
  fin_cases k <;> decide

theorem whitelawPoint_mem_orbit_two : whitelawPoint ∈ whitelawOrbit 2 := by
  exact (coordinatePoint_mem_whitelawOrbit_iff 2 whitelawVector
    whitelawVector_ne_zero).mpr
      ⟨(![1,0,1], 1, 1), -1, whitelawVector_seed_two_coordinates⟩

theorem whitelawPoint_mem : whitelawPoint ∈ whitelawSet :=
  ⟨2, whitelawPoint_mem_orbit_two⟩

theorem whitelawOrbit_subset_generatedOrbit (r : Fin 10) :
    whitelawOrbit r ⊆ MulAction.orbit Model (whitelawSeedPoint r) := by
  rintro p ⟨h, hh⟩
  exact ⟨⟨(h : G2.Model Field), H_le_generated h.property⟩, hh⟩

theorem whitelawSeed_generatedOrbit_eq (r : Fin 10) :
    MulAction.orbit Model (whitelawSeedPoint r) = MulAction.orbit Model whitelawPoint := by
  have hw : whitelawPoint ∈ MulAction.orbit Model (whitelawSeedPoint 2) :=
    whitelawOrbit_subset_generatedOrbit 2 whitelawPoint_mem_orbit_two
  exact (whitelawSeed_generatedOrbit_eq_zero r).trans
    ((whitelawSeed_generatedOrbit_eq_zero 2).symm.trans
      (MulAction.orbit_eq_iff.mpr hw).symm)

/-- Unconditional inclusion in the existing generated-group orbit; the reverse is open. -/
theorem whitelawSet_subset_generatedOrbit :
    whitelawSet ⊆ MulAction.orbit Model whitelawPoint := by
  rintro p ⟨r, hp⟩
  rw [← whitelawSeed_generatedOrbit_eq r]
  exact whitelawOrbit_subset_generatedOrbit r hp

/-- Pair transport in the ambient projective space. No action on W is asserted here. -/
theorem whitelawSet_pair_transport (p q : WhitelawPoints) :
    ∃ g : Model, g • p.val = q.val := by
  obtain ⟨g, hg⟩ := whitelawSet_subset_generatedOrbit p.property
  obtain ⟨h, hh⟩ := whitelawSet_subset_generatedOrbit q.property
  refine ⟨h * g⁻¹, ?_⟩
  rw [← hg, mul_smul, inv_smul_smul]
  exact hh

end Atlas.Janko1

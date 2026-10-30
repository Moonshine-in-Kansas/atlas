import Atlas.Sporadic.Janko1.WhitelawSquareRows

/-!
Uncompiled source-only continuation. Squared coordinates are used only to
remove the complementary permutation or separate distinct seed labels.
The remaining binary sign is determined by an independent unsquared equation.
All stabilizers and orbits are those of the verified actual H action.
-/
noncomputable section
namespace Atlas.Janko1

theorem whitelawSquareMatch_of_transport (r s : Fin 10)
    (t : SignParameters × (Fin 7 × Fin 3)) (c : Field)
    (hc : c • whitelawSeed s = hCoordinateAction t (whitelawSeed r)) :
    WhitelawSquareMatch r s t.2.1 t.2.2 c := by
  intro k
  have he : signCharacter t.1 k *
      (coordinateShift^[t.2.1.val] (coordinateDouble^[t.2.2.val] (whitelawSeed r))) k =
        c * whitelawSeed s k := (congrFun hc k).symm
  have hsign : signCharacter t.1 k ^ 2 = 1 := by
    simpa only [pow_two] using signCharacter_square t.1 k
  have hp := congrArg (fun z : Field => z ^ 2) he
  erw [mul_pow, mul_pow, hsign, one_mul] at hp
  exact hp

set_option maxRecDepth 8192 in
/-- Nine separate seed cases; each decision has eight signs and eleven scalars. -/
theorem remainingSeed_sign_rigid (r : Fin 10) (hr : r ≠ 0) :
    ∀ (a : SignParameters) (c : Field),
      (∀ k : Fin 7, signCharacter a k * whitelawSeed r k = c * whitelawSeed r k) →
        a = 0 := by
  fin_cases r
  · exact (hr rfl).elim
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem remainingSeed_normalForm_fixes_iff (r : Fin 10) (hr : r ≠ 0)
    (t : SignParameters × (Fin 7 × Fin 3)) :
    (hNormalFormEquiv t : G2.Model Field) • whitelawSeedPoint r = whitelawSeedPoint r ↔
      t.1 = 0 ∧ t.2.1 = 0 ∧ t.2.2 = 0 := by
  rcases t with ⟨a, i, j⟩
  constructor
  · intro h
    change (hNormalFormEquiv (a, i, j) : G2.Model Field) •
      coordinatePoint (whitelawSeed r) (whitelawSeed_ne_zero r) =
        coordinatePoint (whitelawSeed r) (whitelawSeed_ne_zero r) at h
    rw [coordinatePoint_smul, coordinatePoint_eq_iff] at h
    obtain ⟨c, hc⟩ := h
    rw [imaginaryCoordinateAction_normalForm] at hc
    have hs := whitelawSquareMatch_of_transport r r (a, i, j) c hc
    obtain ⟨hi, hj⟩ := whitelawSquareMatch_self_rigid r i j c hs
    subst i
    subst j
    have ha : a = 0 := remainingSeed_sign_rigid r hr a c (by
      intro k
      simpa only [hCoordinateAction, Fin.val_zero, Function.iterate_zero_apply,
        Pi.smul_apply, smul_eq_mul] using (congrFun hc k).symm)
    exact ⟨ha, rfl, rfl⟩
  · rintro ⟨ha, hi, hj⟩
    dsimp only at ha hi hj
    subst a
    subst i
    subst j
    rw [hNormalFormEquiv_apply]
    simp only [Fin.val_zero, pow_zero, mul_one]
    change signHom 1 • whitelawSeedPoint r = whitelawSeedPoint r
    rw [map_one, one_smul]

theorem mem_remainingSeed_stabilizer_iff (r : Fin 10) (hr : r ≠ 0) (h : H) :
    h ∈ MulAction.stabilizer H (whitelawSeedPoint r) ↔ h = 1 := by
  constructor
  · intro hf
    obtain ⟨⟨a, i, j⟩, rfl⟩ := hNormalFormEquiv.surjective h
    obtain ⟨ha, hi, hj⟩ := (remainingSeed_normalForm_fixes_iff r hr (a, i, j)).mp hf
    dsimp only at ha hi hj
    subst a
    subst i
    subst j
    apply Subtype.ext
    rw [hNormalFormEquiv_apply]
    simp only [Fin.val_zero, pow_zero, mul_one]
    change signHom 1 = 1
    exact signHom.map_one
  · rintro rfl
    exact (MulAction.stabilizer H (whitelawSeedPoint r)).one_mem

theorem remainingSeed_stabilizer_eq_bot (r : Fin 10) (hr : r ≠ 0) :
    MulAction.stabilizer H (whitelawSeedPoint r) = ⊥ := by
  ext h
  change h ∈ MulAction.stabilizer H (whitelawSeedPoint r) ↔ h = 1
  exact mem_remainingSeed_stabilizer_iff r hr h

theorem whitelawSeed_lt_not_mem_orbit (r s : Fin 10) (hrs : r < s) :
    whitelawSeedPoint s ∉ whitelawOrbit r := by
  intro hp
  obtain ⟨t, c, hc⟩ :=
    (coordinatePoint_mem_whitelawOrbit_iff r (whitelawSeed s) (whitelawSeed_ne_zero s)).mp hp
  exact whitelawSquareMatch_lt_false r s hrs t.2.1 t.2.2 c
    (whitelawSquareMatch_of_transport r s t c hc)

/-- Seed labels coincide exactly when their actual H-orbits meet at a seed. -/
theorem whitelawSeedPoint_mem_orbit_iff (r s : Fin 10) :
    whitelawSeedPoint s ∈ whitelawOrbit r ↔ r = s := by
  constructor
  · intro hp
    rcases lt_trichotomy r s with hrs | hrs | hsr
    · exact (whitelawSeed_lt_not_mem_orbit r s hrs hp).elim
    · exact hrs
    · have hrev : whitelawSeedPoint r ∈ whitelawOrbit s := MulAction.mem_orbit_symm.mp hp
      exact (whitelawSeed_lt_not_mem_orbit s r hsr hrev).elim
  · rintro rfl
    exact MulAction.mem_orbit_self _

theorem whitelawOrbit_disjoint (r s : Fin 10) (hrs : r ≠ s) :
    Disjoint (whitelawOrbit r) (whitelawOrbit s) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  have hpr : MulAction.orbit H p = whitelawOrbit r := MulAction.orbit_eq_iff.mpr hp
  have hps : MulAction.orbit H p = whitelawOrbit s := MulAction.orbit_eq_iff.mpr hq
  have he : whitelawOrbit r = whitelawOrbit s := hpr.symm.trans hps
  have hs : whitelawSeedPoint s ∈ whitelawOrbit r := by
    rw [he]
    exact MulAction.mem_orbit_self _
  exact hrs ((whitelawSeedPoint_mem_orbit_iff r s).mp hs)

theorem whitelawOrbit_pairwise_disjoint :
    Pairwise (fun r s : Fin 10 => Disjoint (whitelawOrbit r) (whitelawOrbit s)) :=
  fun r s hrs => whitelawOrbit_disjoint r s hrs

end Atlas.Janko1

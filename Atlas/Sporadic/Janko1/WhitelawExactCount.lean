import Atlas.Sporadic.Janko1.WhitelawOrbitRigidity

/-!
Uncompiled source-only exact count of the existing ten-orbit Whitelaw set.
The nine new stabilizers and orbit disjointness are proved in the predecessors;
the actual H order and the first 84-point orbit are reused unchanged.
No S-invariance, generated-group transitivity, or sextic claim is made.
-/
noncomputable section
namespace Atlas.Janko1

theorem card_remainingSeed_stabilizer (r : Fin 10) (hr : r ≠ 0) :
    Nat.card (MulAction.stabilizer H (whitelawSeedPoint r)) = 1 := by
  rw [remainingSeed_stabilizer_eq_bot r hr, Subgroup.card_bot]

theorem card_remainingWhitelawOrbit (r : Fin 10) (hr : r ≠ 0) :
    Nat.card (whitelawOrbit r) = 168 := by
  have h := whitelawOrbit_card_mul_stabilizer r
  rw [card_remainingSeed_stabilizer r hr, mul_one] at h
  exact h

theorem card_whitelawOrbit (r : Fin 10) :
    Nat.card (whitelawOrbit r) = if r = 0 then 84 else 168 := by
  by_cases hr : r = 0
  · subst r
    rw [if_pos rfl, card_firstWhitelawOrbit]
  · rw [if_neg hr]
    exact card_remainingWhitelawOrbit r hr

/-- The existing orbit cover is injective because these ten actual orbits are disjoint. -/
theorem whitelawOrbitCover_injective : Function.Injective whitelawOrbitCover := by
  rintro ⟨r, x⟩ ⟨s, y⟩ h
  have hxy : x.val = y.val := congrArg Subtype.val h
  by_cases hrs : r = s
  · subst s
    have he : x = y := Subtype.ext hxy
    subst y
    rfl
  · exact ((Set.disjoint_left.mp (whitelawOrbit_disjoint r s hrs)) x.property
      (hxy.symm ▸ y.property)).elim

/-- Genuine disjoint-orbit decomposition of the already defined point subtype. -/
def whitelawOrbitDecomposition : (Σ r : Fin 10, whitelawOrbit r) ≃ WhitelawPoints :=
  Equiv.ofBijective whitelawOrbitCover
    ⟨whitelawOrbitCover_injective, whitelawOrbitCover_surjective⟩

theorem card_whitelawPoints : Nat.card WhitelawPoints = 1596 := by
  rw [← Nat.card_congr whitelawOrbitDecomposition, Nat.card_sigma]
  simp_rw [card_whitelawOrbit]
  decide

end Atlas.Janko1

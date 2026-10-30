import Atlas.Sporadic.Janko1.ProjectiveGeometry

/-!
Source-only candidate. The ten specified vectors define actual isotropic lines
and an H-invariant union of their orbits. Their disjointness, the nine remaining
stabilizers, S-invariance, and equality with the G-orbit of w0 are not assumed.
-/
noncomputable section
namespace Atlas.Janko1

def whitelawVector : Fin 7 → Field := ![1, 0, -1, 1, 2, 1, 5]

theorem whitelawVector_ne_zero : whitelawVector ≠ 0 := by decide
theorem whitelawVector_norm : ∑ k : Fin 7, whitelawVector k ^ 2 = 0 := by decide

def whitelawPoint : ProjV := coordinatePoint whitelawVector whitelawVector_ne_zero

theorem whitelawPoint_isotropic : IsIsotropic whitelawPoint :=
  (isIsotropic_coordinatePoint _ _).mpr whitelawVector_norm

/-- The ten candidate representatives from §8, in the installed Wilson convention. -/
def whitelawSeed : Fin 10 → (Fin 7 → Field) :=
  ![![0, 0, 1, 0, -2, -4, 1],
    ![0, 1, -3, -2, -2, 0, 2],
    ![0, 1, -1, -1, -1, -2, 5],
    ![0, 1, -1, -3, -3, 2, 3],
    ![0, 1, -1, -3, -5, 2, -2],
    ![0, 1, -2, -1, -3, -2, -5],
    ![0, 1, -3, -5, -2, -1, -2],
    ![1, -1, -3, -2, 2, 3, 4],
    ![1, -1, -4, -2, -4, -1, -4],
    ![1, -1, -2, -5, 2, 4, 2]]

theorem whitelawSeed_ne_zero : ∀ r : Fin 10, whitelawSeed r ≠ 0 := by decide
theorem whitelawSeed_norm : ∀ r : Fin 10, ∑ k : Fin 7, whitelawSeed r k ^ 2 = 0 := by
  decide

def whitelawSeedPoint (r : Fin 10) : ProjV :=
  coordinatePoint (whitelawSeed r) (whitelawSeed_ne_zero r)

theorem whitelawSeedPoint_isotropic (r : Fin 10) : IsIsotropic (whitelawSeedPoint r) :=
  (isIsotropic_coordinatePoint _ _).mpr (whitelawSeed_norm r)

def whitelawOrbit (r : Fin 10) : Set ProjV := MulAction.orbit H (whitelawSeedPoint r)

def whitelawSet : Set ProjV := {p | ∃ r : Fin 10, p ∈ whitelawOrbit r}

abbrev WhitelawPoints := {p : ProjV // p ∈ whitelawSet}

theorem whitelawSeedPoint_mem (r : Fin 10) : whitelawSeedPoint r ∈ whitelawSet :=
  ⟨r, MulAction.mem_orbit_self _⟩

theorem whitelawPoints_isotropic (p : WhitelawPoints) : IsIsotropic p.val := by
  obtain ⟨r, h, hh⟩ := p.property
  rw [← hh]
  exact (isIsotropic_smul_iff (h : G2.Model Field) _).mpr (whitelawSeedPoint_isotropic r)

theorem smul_mem_whitelawSet (h : H) {p : ProjV} (hp : p ∈ whitelawSet) :
    h • p ∈ whitelawSet := by
  obtain ⟨r, k, hk⟩ := hp
  exact ⟨r, h * k, (mul_smul h k _).trans (congrArg (fun x : ProjV => h • x) hk)⟩

instance whitelawHAction : MulAction H WhitelawPoints where
  smul h p := ⟨h • p.val, smul_mem_whitelawSet h p.property⟩
  one_smul p := Subtype.ext (one_smul H p.val)
  mul_smul h k p := Subtype.ext (mul_smul h k p.val)

/-- The finite normal form belongs to the already verified subgroup, not a permutation copy. -/
theorem mem_whitelawOrbit_normalForm (r : Fin 10) (p : ProjV) :
    p ∈ whitelawOrbit r ↔ ∃ t : SignParameters × (Fin 7 × Fin 3),
      (hNormalFormEquiv t : G2.Model Field) • whitelawSeedPoint r = p := by
  constructor
  · rintro ⟨h, hh⟩
    obtain ⟨t, rfl⟩ := hNormalFormEquiv.surjective h
    exact ⟨t, hh⟩
  · rintro ⟨t, ht⟩
    exact ⟨hNormalFormEquiv t, ht⟩

theorem coordinatePoint_mem_whitelawOrbit_iff (r : Fin 10)
    (v : Fin 7 → Field) (hv : v ≠ 0) :
    coordinatePoint v hv ∈ whitelawOrbit r ↔
      ∃ (t : SignParameters × (Fin 7 × Fin 3)) (c : Field),
        c • v = hCoordinateAction t (whitelawSeed r) := by
  rw [mem_whitelawOrbit_normalForm]
  constructor
  · rintro ⟨t, ht⟩
    change (hNormalFormEquiv t : G2.Model Field) •
      coordinatePoint (whitelawSeed r) (whitelawSeed_ne_zero r) = coordinatePoint v hv at ht
    rw [coordinatePoint_smul, coordinatePoint_eq_iff] at ht
    obtain ⟨c, hc⟩ := ht
    exact ⟨t, c, hc.trans (imaginaryCoordinateAction_normalForm t _)⟩
  · rintro ⟨t, c, hc⟩
    refine ⟨t, ?_⟩
    change (hNormalFormEquiv t : G2.Model Field) •
      coordinatePoint (whitelawSeed r) (whitelawSeed_ne_zero r) = coordinatePoint v hv
    rw [coordinatePoint_smul, coordinatePoint_eq_iff]
    exact ⟨c, hc.trans (imaginaryCoordinateAction_normalForm t _).symm⟩

theorem coordinatePoint_mem_whitelawSet_iff (v : Fin 7 → Field) (hv : v ≠ 0) :
    coordinatePoint v hv ∈ whitelawSet ↔
      ∃ (r : Fin 10) (t : SignParameters × (Fin 7 × Fin 3)) (c : Field),
        c • v = hCoordinateAction t (whitelawSeed r) := by
  change (∃ r : Fin 10, coordinatePoint v hv ∈ whitelawOrbit r) ↔ _
  simp only [coordinatePoint_mem_whitelawOrbit_iff]

theorem card_whitelawOrbit_le (r : Fin 10) : Nat.card (whitelawOrbit r) ≤ 168 := by
  have hs : Function.Surjective (fun h : H =>
      (⟨h • whitelawSeedPoint r, h, rfl⟩ : whitelawOrbit r)) := by
    rintro ⟨p, h, rfl⟩
    exact ⟨h, rfl⟩
  exact (Nat.card_le_card_of_surjective _ hs).trans_eq card_H

theorem whitelawOrbit_card_mul_stabilizer (r : Fin 10) :
    Nat.card (whitelawOrbit r) * Nat.card (MulAction.stabilizer H (whitelawSeedPoint r)) =
      168 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H (whitelawSeedPoint r))
  simpa only [whitelawOrbit, Nat.card_prod, card_H] using h

end Atlas.Janko1

import ComparisonWork.J1WhitelawSeedTransport

/-!
Uncompiled source-only reduction of the remaining J1-O5 obligation. No theorem
in this file assumes that the finite rows have been discharged. The final iff
identifies the exact missing rows needed for W = G.w0. It preserves W and G.
-/
noncomputable section
namespace Atlas.Janko1

/-- Exactly one of the 10 times 8 remaining local membership obligations.
The scalar/sign equation is unsquared; no sign information is discarded. -/
abbrev WhitelawSRow (r : Fin 10) (a : SignParameters) : Prop :=
  ∃ (s : Fin 10) (t : SignParameters × (Fin 7 × Fin 3)) (c : Field),
    c • sCoordinateAction (signedWhitelawSeed r a) =
      hCoordinateAction t (whitelawSeed s)

theorem whitelawSRow_of_transport {r s : Fin 10} {a b : SignParameters}
    {i : Fin 7} {j : Fin 3} {c : Field}
    (ht : WhitelawSTransport r s a b i j c) : WhitelawSRow r a :=
  ⟨s, (b, i, j), c, ht⟩

theorem S_signedSeed_mem_whitelawSet_iff (r : Fin 10) (a : SignParameters) :
    S • (signElement a • whitelawSeedPoint r) ∈ whitelawSet ↔ WhitelawSRow r a := by
  change S • (signElement a •
    coordinatePoint (whitelawSeed r) (whitelawSeed_ne_zero r)) ∈ whitelawSet ↔ _
  rw [coordinatePoint_smul, coordinatePoint_smul, coordinatePoint_mem_whitelawSet_iff]
  simp only [imaginaryCoordinateAction_S, imaginaryCoordinateAction_sign,
    WhitelawSRow, signedWhitelawSeed]
  rfl

/-- S normalizes C, and H = C E. Thus the C-factor can be moved to the output. -/
theorem S_preserves_whitelawSet_iff_signedSeeds :
    (∀ p : ProjV, p ∈ whitelawSet → S • p ∈ whitelawSet) ↔
      ∀ (r : Fin 10) (a : SignParameters),
        S • (signElement a • whitelawSeedPoint r) ∈ whitelawSet := by
  constructor
  · intro hS r a
    exact hS _ (smul_mem_whitelawSet
      ⟨signElement a, signSubgroup_le_H (signElement_mem_signSubgroup a)⟩
      (whitelawSeedPoint_mem r))
  · intro hrows p hp
    obtain ⟨r, h, hh⟩ := hp
    obtain ⟨c, a, hf⟩ := H_right_sign_factorization h
    let d : pqSubgroup :=
      ⟨S * (c : G2.Model Field) * S⁻¹,
        (Subgroup.mem_normalizer_iff.mp S_mem_pqSubgroup_normalizer
          (c : G2.Model Field)).mp c.property⟩
    have he : S * (h : G2.Model Field) =
        (d : G2.Model Field) * (S * signElement a) := by
      rw [hf]
      dsimp only [d]
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [← hh]
    change S • ((h : G2.Model Field) • whitelawSeedPoint r) ∈ whitelawSet
    rw [← mul_smul, he,
      mul_smul (d : G2.Model Field) (S * signElement a) (whitelawSeedPoint r),
      mul_smul S (signElement a) (whitelawSeedPoint r)]
    let dH : H := ⟨(d : G2.Model Field), pqSubgroup_le_H d.property⟩
    have hd := smul_mem_whitelawSet dH (hrows r a)
    change (d : G2.Model Field) • (S • (signElement a • whitelawSeedPoint r)) ∈
      whitelawSet at hd
    exact hd

theorem S_preserves_whitelawSet_iff_rows :
    (∀ p : ProjV, p ∈ whitelawSet → S • p ∈ whitelawSet) ↔
      ∀ (r : Fin 10) (a : SignParameters), WhitelawSRow r a := by
  rw [S_preserves_whitelawSet_iff_signedSeeds]
  simp only [S_signedSeed_mem_whitelawSet_iff]

theorem H_smul_mem_whitelawSet_iff (h : H) (p : ProjV) :
    h • p ∈ whitelawSet ↔ p ∈ whitelawSet := by
  constructor
  · intro hp
    simpa only [inv_smul_smul] using smul_mem_whitelawSet h⁻¹ hp
  · exact smul_mem_whitelawSet h

/-- Ordinary closure induction. Its S-premise is explicit and remains to be proved. -/
theorem generated_smul_mem_whitelawSet_of_S
    (hS : ∀ p : ProjV, p ∈ whitelawSet → S • p ∈ whitelawSet)
    (g : Model) (p : ProjV) : g • p ∈ whitelawSet ↔ p ∈ whitelawSet := by
  have hS' (p : ProjV) : S • p ∈ whitelawSet ↔ p ∈ whitelawSet := by
    constructor
    · intro hp
      simpa only [S_smul_S] using hS (S • p) hp
    · exact hS p
  have hall : ∀ (x : G2.Model Field), x ∈ generated →
      ∀ p : ProjV, x • p ∈ whitelawSet ↔ p ∈ whitelawSet := by
    intro x hx
    change x ∈ Subgroup.closure ({P, Q, R, S} : Set (G2.Model Field)) at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      intro p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact H_smul_mem_whitelawSet_iff ⟨P, Subgroup.subset_closure (by simp)⟩ p
      · exact H_smul_mem_whitelawSet_iff ⟨Q, Subgroup.subset_closure (by simp)⟩ p
      · exact H_smul_mem_whitelawSet_iff ⟨R, Subgroup.subset_closure (by simp)⟩ p
      · exact hS' p
    | one =>
      intro p
      rw [one_smul]
    | mul x y hx hy ihx ihy =>
      intro p
      rw [mul_smul, ihx, ihy]
    | inv x hx ih =>
      intro p
      simpa only [smul_inv_smul] using (ih (x⁻¹ • p)).symm
  exact hall (g : G2.Model Field) g.property p

/-- The reverse orbit inclusion, conditional only on the precisely named S-step. -/
theorem whitelawSet_eq_generatedOrbit_of_S
    (hS : ∀ p : ProjV, p ∈ whitelawSet → S • p ∈ whitelawSet) :
    whitelawSet = MulAction.orbit Model whitelawPoint := by
  apply Set.Subset.antisymm whitelawSet_subset_generatedOrbit
  rintro p ⟨g, rfl⟩
  exact (generated_smul_mem_whitelawSet_of_S hS g whitelawPoint).mpr whitelawPoint_mem

/-- Exact endpoint reduction, with no invariance, order, or cardinality assumption. -/
theorem whitelawSet_eq_generatedOrbit_iff_rows :
    whitelawSet = MulAction.orbit Model whitelawPoint ↔
      ∀ (r : Fin 10) (a : SignParameters), WhitelawSRow r a := by
  constructor
  · intro he
    apply S_preserves_whitelawSet_iff_rows.mp
    intro p hp
    rw [he] at hp ⊢
    exact MulAction.mem_orbit_of_mem_orbit (⟨S, S_mem⟩ : Model) hp
  · intro hrows
    exact whitelawSet_eq_generatedOrbit_of_S (S_preserves_whitelawSet_iff_rows.mpr hrows)

end Atlas.Janko1

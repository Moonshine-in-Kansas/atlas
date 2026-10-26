import Atlas.LinearGroups.Unitary.GeneratedNormOneTransport

/-! Uniform transvection generation in dimensions at least three over q>2,
via actual coordinate blocks and norm-one stabilizers. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Support descent and the actual SU(n−1) stabilizer give generation in all
higher dimensions. The exceptional binary three-dimensional case is excluded. -/
theorem transvectionGenerated_add_three_eq_top (hdeg : Module.finrank F K = 2)
    (hq : 2 < Nat.card F) (k : ℕ) :
    transvectionGenerated hdeg (n := 3+k) = ⊤ := by
  classical
  induction k with
  | zero => exact transvectionGenerated_three_eq_top hdeg hq
  | succ k ih =>
    apply top_unique
    intro g _
    let v := g.val *ᵥ (Pi.single 0 1 : Fin (3+(k+1)) → K)
    have hv : hermitian F K v v = 1 := by
      exact (u_preserves_hermitian hdeg (⟨g.val,g.prop.1⟩ : U F K (3+(k+1)) hdeg)
        _ _).trans (by simp)
    obtain ⟨h,hh,he⟩ := exists_generated_map_to_first hdeg hq v hv
    have hk : h*g ∈ firstSpecialStabilizer (n := 3+k) hdeg := by
      change (h*g) • coordinateUnit (F := F) (K := K) 0 = coordinateUnit 0
      apply Subtype.ext
      change (h.val*g.val) *ᵥ Pi.single 0 1 = Pi.single 0 1
      rwa [← mulVec_mulVec]
    have hkH := firstSpecialStabilizer_le_generated hdeg ih hk
    simpa using (transvectionGenerated hdeg).mul_mem
      ((transvectionGenerated hdeg).inv_mem hh) hkH

/-- Actual special-unitary generation for every n≥3 and q>2. -/
theorem transvectionGenerated_eq_top_of_three_le (hdeg : Module.finrank F K = 2)
    (hq : 2 < Nat.card F) {n : ℕ} (hn : 3 ≤ n) :
    transvectionGenerated hdeg (n := n) = ⊤ := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  exact transvectionGenerated_add_three_eq_top hdeg hq k
end Atlas.Unitary

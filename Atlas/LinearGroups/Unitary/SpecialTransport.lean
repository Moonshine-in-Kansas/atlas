import Atlas.LinearGroups.Unitary.SpecialStabilizer
import Atlas.LinearGroups.Unitary.NormOneTransport

/-! # Special-unitary transitivity on the norm-one shell

The determinant is corrected inside the actual orthogonal complement. This
uses the already proved full-unitary transport, not transvection generation.
-/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

theorem determinant_extendUnitary (hdeg : Module.finrank F K = 2) (g : U F K n hdeg) :
    determinant hdeg (extendUnitary hdeg g).val = determinant hdeg g := by
  apply Subtype.ext
  apply Units.ext
  exact det_extendMatrix g.val

/-- In dimension at least two, the determinant can be corrected in the
complement while the first norm-one vector remains fixed. -/
theorem exists_special_map_from_first (hdeg : Module.finrank F K = 2) (hn : 0 < n)
    (v : Fin (n + 1) → K) (hv : hermitian F K v v = 1) :
    ∃ g : SU F K (n + 1) hdeg, g.val *ᵥ Pi.single 0 1 = v := by
  obtain ⟨g, hg⟩ := exists_unitary_map hdeg (Pi.single 0 1) v (by simp) hv
  obtain ⟨k, hk⟩ := determinant_surjective (n := n) hdeg hn (determinant hdeg g)⁻¹
  let t : U F K (n + 1) hdeg := g * (extendUnitary hdeg k).val
  have ht : determinant hdeg t = 1 := by
    rw [show t = g * (extendUnitary hdeg k).val from rfl, map_mul,
      determinant_extendUnitary, hk, mul_inv_cancel]
  refine ⟨⟨t.val, t.prop, ?_⟩, ?_⟩
  · exact congrArg (fun a : normOne F K => (a.val : K)) ht
  · change (g.val * (extendUnitary hdeg k).val.val) *ᵥ Pi.single 0 1 = v
    rw [← mulVec_mulVec]
    have hf : (extendUnitary hdeg k).val.val *ᵥ Pi.single 0 1 = Pi.single 0 1 :=
      congrArg Subtype.val (extendUnitary hdeg k).prop
    rw [hf]
    exact hg

/-- Actual SU transport on the standard norm-one vectors, uniformly in q. -/
theorem exists_special_unitary_map (hdeg : Module.finrank F K = 2) (hn : 2 ≤ n)
    (v w : Fin n → K) (hv : hermitian F K v v = 1) (hw : hermitian F K w w = 1) :
    ∃ g : SU F K n hdeg, g.val *ᵥ v = w := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hk : 0 < k := by omega
  obtain ⟨a, ha⟩ := exists_special_map_from_first hdeg hk v hv
  obtain ⟨b, hb⟩ := exists_special_map_from_first hdeg hk w hw
  let vv : NormOneVectors F K (k + 1) := ⟨v, hv⟩
  let ww : NormOneVectors F K (k + 1) := ⟨w, hw⟩
  let e := coordinateUnit (F := F) (K := K) (0 : Fin (k + 1))
  have ha' : a • e = vv := Subtype.ext ha
  have hb' : b • e = ww := Subtype.ext hb
  refine ⟨b * a⁻¹, ?_⟩
  have h : (b * a⁻¹) • vv = ww := by
    rw [← ha', mul_smul, inv_smul_smul, hb']
  exact congrArg Subtype.val h

end Atlas.Unitary

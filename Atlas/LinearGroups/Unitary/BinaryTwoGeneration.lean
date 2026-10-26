import Atlas.LinearGroups.Unitary.BinaryNormOneTransport
import Atlas.LinearGroups.Unitary.BlockEmbeddings

/-! The binary two-dimensional generation base, from the determinant-one
one-dimensional stabilizer and the actual root action. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem special_one_eq_one (hdeg : Module.finrank F K = 2) (g : SU F K 1 hdeg) :
    g = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i
  fin_cases j
  have hd : g.val.det = 1 := g.prop.2
  change g.val 0 0 = 1
  exact (Matrix.det_fin_one g.val).symm.trans hd

theorem transvectionGenerated_one_eq_top (hdeg : Module.finrank F K = 2) :
    transvectionGenerated hdeg (n := 1) = ⊤ := by
  apply top_unique
  intro g _
  rw [special_one_eq_one hdeg g]
  exact (transvectionGenerated hdeg).one_mem

theorem binary_transvectionGenerated_two_eq_top (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) : transvectionGenerated hdeg (n := 2) = ⊤ := by
  letI := binary_charP hdeg hq
  apply top_unique
  intro g _
  let v := g.val *ᵥ (Pi.single 0 1 : Fin 2 → K)
  have hv : hermitian F K v v = 1 := by
    exact (u_preserves_hermitian hdeg (⟨g.val,g.prop.1⟩ : U F K 2 hdeg) _ _).trans (by simp)
  obtain ⟨h,hh,he⟩ := binary_even_generated_map_to_first hdeg hq (by decide : Even 2)
    (by decide) v hv
  have hk : h*g ∈ firstSpecialStabilizer (n := 1) hdeg := by
    change (h*g) • coordinateUnit (F := F) (K := K) 0 = coordinateUnit 0
    apply Subtype.ext
    change (h.val*g.val) *ᵥ Pi.single 0 1 = Pi.single 0 1
    rwa [← mulVec_mulVec]
  have hkH := firstSpecialStabilizer_le_generated hdeg (transvectionGenerated_one_eq_top hdeg) hk
  simpa using (transvectionGenerated hdeg).mul_mem
    ((transvectionGenerated hdeg).inv_mem hh) hkH
end Atlas.Unitary

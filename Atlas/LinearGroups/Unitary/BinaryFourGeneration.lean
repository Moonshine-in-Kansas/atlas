import Atlas.LinearGroups.Unitary.BinaryTwoGeneration
import Atlas.LinearGroups.Unitary.BinaryThreeDenseTransport

/-! Structural closure of the binary rank-four generation argument. The dense
three-coordinate transporter is isolated as the explicit Fourier bridge input. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- A dense Fourier bridge together with ordinary root transport on vectors
having a zero coordinate gives the full complementary norm-one action. -/
theorem binary_three_extended_transport_of_dense (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2)
    (hdense : ∀ v : Fin 3 → K, (∀ i, v i ≠ 0) →
      ∃ g : SU F K 3 hdeg, extendSpecialHom hdeg g ∈ transvectionGenerated hdeg ∧
        g.val *ᵥ v = Pi.single 0 (v 0))
    (v : Fin 3 → K) (hv : hermitian F K v v = 1) :
    ∃ g : SU F K 3 hdeg, extendSpecialHom hdeg g ∈ transvectionGenerated hdeg ∧
      g.val *ᵥ v = Pi.single 0 1 := by
  classical
  letI := binary_charP hdeg hq
  by_cases hzero : ∃ i, v i = 0
  · obtain ⟨g,hg,he⟩ := charTwo_generated_map_to_first_of_zero hdeg (by decide) v hv hzero
    exact ⟨g,extendSpecialHom_generated hdeg g hg,he⟩
  · push_neg at hzero
    obtain ⟨g,hg,he⟩ := hdense v hzero
    have hv' : hermitian F K (g.val *ᵥ v) (g.val *ᵥ v) = 1 :=
      (u_preserves_hermitian hdeg (⟨g.val,g.prop.1⟩ : U F K 3 hdeg) v v).trans hv
    have hz : ∃ i, (g.val *ᵥ v) i = 0 := by
      refine ⟨1, ?_⟩
      rw [he]
      simp
    obtain ⟨h,hh,heh⟩ := charTwo_generated_map_to_first_of_zero hdeg (by decide)
      (g.val *ᵥ v) hv' hz
    refine ⟨h*g, ?_, ?_⟩
    · rw [map_mul]
      exact (transvectionGenerated hdeg).mul_mem (extendSpecialHom_generated hdeg h hh) hg
    · change (h.val*g.val) *ᵥ v = _
      rwa [← mulVec_mulVec]

/-- The binary SU₂ stabilizer and the complementary norm-one action exhaust
all of the genuine SU₃ stabilizer inside the upper generated subgroup. -/
theorem binary_firstStabilizer_le_generated_of_transport (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2)
    (htransport : ∀ v : Fin 3 → K, hermitian F K v v = 1 →
      ∃ g : SU F K 3 hdeg, extendSpecialHom hdeg g ∈ transvectionGenerated hdeg ∧
        g.val *ᵥ v = Pi.single 0 1) :
    firstSpecialStabilizer (n := 3) hdeg ≤ transvectionGenerated hdeg := by
  have hall (g : SU F K 3 hdeg) : extendSpecialHom hdeg g ∈ transvectionGenerated hdeg := by
    let v := g.val *ᵥ (Pi.single 0 1 : Fin 3 → K)
    have hv : hermitian F K v v = 1 :=
      (u_preserves_hermitian hdeg (⟨g.val,g.prop.1⟩ : U F K 3 hdeg) _ _).trans (by simp)
    obtain ⟨h,hh,he⟩ := htransport v hv
    have hk : h*g ∈ firstSpecialStabilizer (n := 2) hdeg := by
      change (h*g) • coordinateUnit (F := F) (K := K) 0 = coordinateUnit 0
      apply Subtype.ext
      change (h.val*g.val) *ᵥ Pi.single 0 1 = Pi.single 0 1
      rwa [← mulVec_mulVec]
    have hkgen := firstSpecialStabilizer_le_generated hdeg
      (binary_transvectionGenerated_two_eq_top hdeg hq) hk
    have hext := extendSpecialHom_generated hdeg (h*g) hkgen
    have hmem := (transvectionGenerated hdeg).mul_mem
      ((transvectionGenerated hdeg).inv_mem hh) hext
    simpa only [map_mul, inv_mul_cancel_left] using hmem
  intro g hg
  let k := firstSpecialStabilizerEquiv hdeg ⟨g,hg⟩
  have he : extendSpecialHom hdeg k = g :=
    congrArg Subtype.val ((firstSpecialStabilizerEquiv hdeg).symm_apply_apply ⟨g,hg⟩)
  exact he ▸ hall k

/-- Actual binary rank-four generation once the explicit dense Fourier
transporter has been supplied. No abstract recognition or group order is used. -/
theorem binary_four_generation_of_dense (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2)
    (hdense : ∀ v : Fin 3 → K, (∀ i, v i ≠ 0) →
      ∃ g : SU F K 3 hdeg, extendSpecialHom hdeg g ∈ transvectionGenerated hdeg ∧
        g.val *ᵥ v = Pi.single 0 (v 0)) :
    transvectionGenerated hdeg (n := 4) = ⊤ := by
  letI := binary_charP hdeg hq
  have hstab := binary_firstStabilizer_le_generated_of_transport hdeg hq
    (binary_three_extended_transport_of_dense hdeg hq hdense)
  apply top_unique
  intro g _
  let v := g.val *ᵥ (Pi.single 0 1 : Fin 4 → K)
  have hv : hermitian F K v v = 1 :=
    (u_preserves_hermitian hdeg (⟨g.val,g.prop.1⟩ : U F K 4 hdeg) _ _).trans (by simp)
  obtain ⟨h,hh,he⟩ := binary_even_generated_map_to_first hdeg hq (by decide : Even 4)
    (by decide) v hv
  have hk : h*g ∈ firstSpecialStabilizer (n := 3) hdeg := by
    change (h*g) • coordinateUnit (F := F) (K := K) 0 = coordinateUnit 0
    apply Subtype.ext
    change (h.val*g.val) *ᵥ Pi.single 0 1 = Pi.single 0 1
    rwa [← mulVec_mulVec]
  simpa using (transvectionGenerated hdeg).mul_mem
    ((transvectionGenerated hdeg).inv_mem hh) (hstab hk)
/-- The actual binary special unitary group in dimension four is generated
by its Hermitian transvections. -/
theorem binary_transvectionGenerated_four_eq_top (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) : transvectionGenerated hdeg (n := 4) = ⊤ := by
  letI := binary_charP hdeg hq
  exact binary_four_generation_of_dense hdeg hq
    (binary_dense_complement_transport hdeg hq)
end Atlas.Unitary

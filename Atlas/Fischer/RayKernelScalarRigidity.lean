import Atlas.Fischer.RayKernelPhaseRigidity
import Atlas.Fischer.ReflectingNonrealExistence
import Atlas.Fischer.ReflectingFamilyMoments

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Nonreal displayed octadic pairings exclude conjugate-linear elements from
the actual ray kernel. -/
theorem semilinearRayKernel_parity_zero (e : SemilinearAlgebraAutomorphism)
    (he : e ∈ semilinearRayKernel) : semilinearAlgebraParity e=0 := by
  classical
  obtain ⟨a,ha,hact⟩ := semilinearRayKernel_common_phase e he
  obtain ⟨Ov,hOv⟩ := Finset.card_pos.mp (show 0 < octads.card by rw [octads_card]; decide)
  let O : Octad := ⟨Ov,hOv⟩
  obtain ⟨F,hF⟩ := octad_exists_disjoint O
  obtain ⟨χ,ψ,hn⟩ := octadicRoot_disjoint_exists_nonreal O F hF
    (chosenOctadCalibration O) (chosenOctadCalibration F)
  have hh := semilinearAlgebraAutomorphism_hermitian e
    (octadicRoot (chosenOctadCalibration O) χ) (octadicRoot (chosenOctadCalibration F) ψ)
  have hO := hact (.inr (.inl ⟨O,χ⟩))
  have hG := hact (.inr (.inl ⟨F,ψ⟩))
  change e.val (octadicRoot _ χ)=_ at hO
  change e.val (octadicRoot _ ψ)=_ at hG
  rw [hO,hG,hermitian_smul_left,hermitian_smul_right] at hh
  have hu := cube_root_unit_norm ha
  have hp : semilinearAlgebraParity e=0 ∨ semilinearAlgebraParity e=1 := by
    have h : ∀ b : Bit, b=0 ∨ b=1 := by decide
    exact h _
  rcases hp with hp | hp
  · exact hp
  · rw [hp] at hh
    have hz (z : Scalar) : a * (star a * z) = z := by
      calc
        a * (star a * z) = (star a * a) * z := by ring
        _ = z := by rw [hu,one_mul]
    simp only [reflectingRootParameterVector] at hh
    rw [hz] at hh
    exact False.elim (hn (by simpa using hh.symm))

/-- The kernel of the actual ray action consists exactly of global cubic scalar
maps; scalar linearity is derived, not imposed in its definition. -/
theorem mem_semilinearRayKernel_scalar_iff (e : SemilinearAlgebraAutomorphism) :
    e ∈ semilinearRayKernel ↔ ∃ a : Mu3, ∀ x : Coordinates, e.val x=a.val.val • x := by
  constructor
  · intro he
    obtain ⟨a,ha,hact⟩ := semilinearRayKernel_common_phase e he
    refine ⟨rootsOfUnity.mkOfPowEq a ha,?_⟩
    intro x
    change e.val x=a • x
    have hx : x ∈ Submodule.span Scalar (Set.range reflectingRootParameterVector) := by
      rw [reflectingFamily_span]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨t,rfl⟩ := hx; exact hact t
    | zero => simp [semilinearAlgebra_map_zero]
    | add x y hx hy ihx ihy => rw [e.property.1,ihx,ihy,smul_add]
    | smul c x hx ih =>
      rw [semilinearAlgebraParity_spec,semilinearRayKernel_parity_zero e he,ih]
      simp only [scalarParityAut_zero]
      exact smul_comm c a x
  · rintro ⟨a,ha⟩
    apply (mem_semilinearRayKernel_phase_iff e).mpr
    intro t
    exact ⟨a.val.val,(mem_rootsOfUnity' _ _).mp a.property,ha _⟩

end Atlas.Fischer

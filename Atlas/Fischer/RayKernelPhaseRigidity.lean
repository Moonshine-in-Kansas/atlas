import Atlas.Fischer.SemilinearRayAction
import Atlas.Fischer.ReflectingRootBasicSupport
import Atlas.Fischer.IntrinsicTraceForm

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- A pairing equal to one forces equal phases even for a conjugate-linear
algebra automorphism. -/
theorem semilinear_fixed_phase_pairing_one (e : SemilinearAlgebraAutomorphism)
    (r s : Coordinates) (a b : Scalar) (hb : b^3=1)
    (hr : e.val r=a • r) (hs : e.val s=b • s) (hrs : hermitian r s=1) : a=b := by
  have h := semilinearAlgebraAutomorphism_hermitian e r s
  rw [hr,hs,hermitian_smul_left,hermitian_smul_right,hrs,map_one] at h
  have hn := cube_root_unit_norm hb
  calc
    a = a * (star b * b) := by rw [hn,mul_one]
    _ = (a * (star b * 1)) * b := by ring
    _ = b := by rw [h,one_mul]

/-- The actual basic representatives connect every displayed representative
by pairings equal to one. -/
theorem reflectingRootParameter_basic_neighbor (t : ReflectingRootParameter) :
    ∃ i : Omega, hermitian (basicAxis i) (reflectingRootParameterVector t)=1 := by
  classical
  rcases t with j | (⟨O,χ⟩ | ⟨p,ξ⟩)
  · obtain ⟨i,hi⟩ := exists_ne j
    exact ⟨i,by simp [reflectingRootParameterVector,hermitian_basicAxis_basicAxis,hi]⟩
  · obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < O.val.card by rw [octad_size O.val O.property]; decide)
    exact ⟨i,by simp [reflectingRootParameterVector,hermitian_basicAxis_octadic,hi]⟩
  · obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < p.val.card by rw [p.property]; decide)
    exact ⟨i,by simp [reflectingRootParameterVector,hermitian_basicAxis_duadic,hi]⟩

/-- Every ray-kernel element has a single common cubic phase on the whole
actual displayed family. This does not yet presume its scalar parity is zero. -/
theorem semilinearRayKernel_common_phase (e : SemilinearAlgebraAutomorphism)
    (he : e ∈ semilinearRayKernel) : ∃ a : Scalar, a^3=1 ∧
      ∀ t, e.val (reflectingRootParameterVector t)=a • reflectingRootParameterVector t := by
  classical
  choose a ha hact using (mem_semilinearRayKernel_phase_iff e).mp he
  let i0 : Omega := Classical.choice inferInstance
  have hbasic (i : Omega) : a (.inl i)=a (.inl i0) := by
    by_cases hi : i=i0
    · subst i; rfl
    · exact semilinear_fixed_phase_pairing_one e _ _ _ _ (ha (.inl i0))
        (hact (.inl i)) (hact (.inl i0)) (by simp [reflectingRootParameterVector,hermitian_basicAxis_basicAxis,hi])
  refine ⟨a (.inl i0),ha (.inl i0),?_⟩
  intro t
  obtain ⟨i,hi⟩ := reflectingRootParameter_basic_neighbor t
  have ht := semilinear_fixed_phase_pairing_one e _ _ _ _ (ha t) (hact (.inl i)) (hact t) hi
  rw [hact,← ht,hbasic]

end Atlas.Fischer

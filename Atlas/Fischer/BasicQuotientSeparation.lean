import Atlas.Fischer.RootPairQuotientOrders
import Atlas.Fischer.BasicSupportExceptOne

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The two-group quotient argument retains the entire commuting profile. -/
theorem basic_quotient_separation_two {H : Type*} [Group H]
    (f : rootGeneratedRayGroup →* H) (hk : IsPGroup 2 f.ker)
    (i : Omega) (t : ReflectingRootParameter)
    (he : f (distinguishedRootElement t)=f (distinguishedRootElement (.inl i))) : t=.inl i := by
  have hprofile (u : ReflectingRootParameter) :
      (hermitian (reflectingRootParameterVector u) (reflectingRootParameterVector t) ≠ 0) ↔
      (hermitian (reflectingRootParameterVector u) (basicAxis i) ≠ 0) := by
    change (hermitian (reflectingRootParameterVector u) (reflectingRootParameterVector t) ≠ 0) ↔
      (hermitian (reflectingRootParameterVector u) (reflectingRootParameterVector (.inl i)) ≠ 0)
    rw [← distinguishedRootElement_quotient_square_iff f hk (by decide : 2 ≠ 3) u t,
      ← distinguishedRootElement_quotient_square_iff f hk (by decide : 2 ≠ 3) u (.inl i)]
    simp only [map_mul,he]
  obtain ⟨j,rfl⟩ := displayedRoot_full_basic_support t (fun a => by
    apply (hprofile (.inl a)).mpr
    change hermitian (basicAxis a) (basicAxis i) ≠ 0
    rw [hermitian_basicAxis_basicAxis]
    split_ifs <;> norm_num)
  by_contra hij
  have hji : j ≠ i := by simpa using hij
  obtain ⟨u,hu,hv⟩ := basic_axes_separated_by_octadic j i hji
  have hleft : hermitian (reflectingRootParameterVector (.inr (.inl u))) (basicAxis j) ≠ 0 := by
    rw [← hermitian_star]
    change star (hermitian (basicAxis j) (octadicRoot (chosenOctadCalibration u.1) u.2)) ≠ 0
    rw [hu,star_one]
    norm_num
  have hright := (hprofile (.inr (.inl u))).mp hleft
  rw [← hermitian_star] at hright
  change star (hermitian (basicAxis i) (octadicRoot (chosenOctadCalibration u.1) u.2)) ≠ 0 at hright
  rw [hv,star_zero] at hright
  exact hright rfl

/-- For a three-group quotient, twenty-three surviving basic involution pairs
force a putative conjugate back into the basic frame. -/
theorem basic_quotient_separation_three {H : Type*} [Group H]
    (f : rootGeneratedRayGroup →* H) (hk : IsPGroup 3 f.ker)
    (i : Omega) (t : ReflectingRootParameter)
    (he : f (distinguishedRootElement t)=f (distinguishedRootElement (.inl i))) : t=.inl i := by
  have ho (j : Omega) (hji : j ≠ i) :
      orderOf (f (distinguishedRootElement (.inl j) * distinguishedRootElement t))=2 := by
    rw [map_mul,he,← map_mul]
    exact basic_pair_quotient_order f hk (by decide : 3 ≠ 2) j i hji
  obtain ⟨j,rfl⟩ := displayedRoot_basic_support_except_one t i (fun a hai => by
    intro hz
    have hd := orderOf_map_dvd f (distinguishedRootElement (.inl a) * distinguishedRootElement t)
    rw [ho a hai,distinguishedRootElement_zero_order (.inl a) t hz] at hd
    norm_num at hd)
  by_contra hji
  have hji' : j ≠ i := by simpa using hji
  have h := ho j hji'
  rw [distinguishedRootElement_mul_self,map_one,orderOf_one] at h
  norm_num at h

end Atlas.Fischer

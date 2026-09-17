import Atlas.Conway.EisensteinBalancedTransitive

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

theorem eisensteinBalanced_phase_base_mem (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (t : ternaryGolay) :
    eisensteinPhaseIsometries (Multiplicative.ofAdd t) • eisensteinBalancedBaseFrame c j ∈
      eisensteinBalancedFamily := by
  rw [eisensteinBalancedFrame_phase]
  exact eisensteinBalancedParameterFrame_mem _

theorem eisensteinBalancedFamily_phase_invariant (t : ternaryGolay)
    (F : EisensteinFrame) (hF : F ∈ eisensteinBalancedFamily) :
    eisensteinPhaseIsometries (Multiplicative.ofAdd t) • F ∈ eisensteinBalancedFamily := by
  obtain ⟨p,rfl⟩ := (eisensteinBalancedFamily_mem_iff F).mp hF
  obtain ⟨s,hs⟩ := eisensteinBalancedFrame_phase_exists p
  rw [← hs,← mul_smul,← map_mul]
  exact eisensteinBalanced_phase_base_mem p.1 p.2.1 (t+s)

theorem eisensteinBalancedFamily_coordinate_invariant (g : TernaryPureAutomorphism)
    (F : EisensteinFrame) (hF : F ∈ eisensteinBalancedFamily) :
    eisensteinCoordinateIsometries g • F ∈ eisensteinBalancedFamily := by
  obtain ⟨p,rfl⟩ := (eisensteinBalancedFamily_mem_iff F).mp hF
  obtain ⟨s,hs⟩ := eisensteinBalancedFrame_phase_exists p
  let d := ternaryBalancedPermutation g p.1
  let k : ternarySupport d.val.val := ⟨g.val p.2.1.val,by
    change g.val p.2.1.val ∈ ternarySupport (fun i => p.1.val.val (g.val.symm i))
    rw [ternarySupport_permute]
    exact Finset.mem_map.mpr ⟨p.2.1.val,p.2.1.prop,rfl⟩⟩
  have hc := eisensteinBalancedBaseFrame_coordinate p.1 d p.2.1 k g (fun _ => rfl) rfl
  have he := DFunLike.congr_fun (eisensteinCoordinate_phase_conjugation g) (Multiplicative.ofAdd s)
  change eisensteinPhaseIsometries (eisensteinCodeActionHom g (Multiplicative.ofAdd s)) =
    eisensteinCoordinateIsometries g*eisensteinPhaseIsometries (Multiplicative.ofAdd s)*
      (eisensteinCoordinateIsometries g)⁻¹ at he
  have hm : eisensteinCoordinateIsometries g*eisensteinPhaseIsometries (Multiplicative.ofAdd s) =
      eisensteinPhaseIsometries (eisensteinCodeActionHom g (Multiplicative.ofAdd s))*
        eisensteinCoordinateIsometries g := by rw [he]; group
  rw [← hs,← mul_smul,hm,mul_smul,hc]
  exact eisensteinBalanced_phase_base_mem d k _

theorem eisensteinBalancedFamily_invariant (g : eisensteinCoordinateFrameStabilizer)
    (F : EisensteinFrame) (hF : F ∈ eisensteinBalancedFamily) :
    g.val • F ∈ eisensteinBalancedFamily := by
  obtain ⟨p,rfl⟩ := eisensteinFrameFromParameters_surjective g
  rcases p with ⟨b,t,g⟩
  have hm := eisensteinBalancedFamily_phase_invariant t _
    (eisensteinBalancedFamily_coordinate_invariant g F hF)
  change eisensteinMonomialParameterIsometry (b,t,g) • F ∈ _
  cases b <;> simpa [eisensteinMonomialParameterIsometry,mul_smul,eisensteinSign_frame] using hm

/-- The balanced-heavy family is an actual suborbit, of size 17820. -/
theorem eisensteinBalancedFamily_orbit (F : EisensteinFrame) (hF : F ∈ eisensteinBalancedFamily) :
    MulAction.orbit eisensteinCoordinateFrameStabilizer F =
      (eisensteinBalancedFamily : Set EisensteinFrame) := by
  ext G
  constructor
  · rintro ⟨g,rfl⟩
    exact eisensteinBalancedFamily_invariant g F hF
  · intro hG
    obtain ⟨g,hg⟩ := eisensteinBalancedFamily_transitive F G hF hG
    exact ⟨g,hg⟩

end Atlas.Conway

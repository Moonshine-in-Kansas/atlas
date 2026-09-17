import Atlas.Mathieu.TernaryPhaseAction
import Atlas.GroupTheory.NonabelianSimplePerfect

noncomputable section
namespace Atlas.Codes

def ternaryPurePhaseEndHom : TernaryPureAutomorphism →*
    Module.End (ZMod 3) TernaryPhaseModule where
  toFun := ternaryPurePhaseEnd
  map_one' := by
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := Submodule.Quotient.mk_surjective ternaryConstants v
    change ternaryConstants.mkQ (ternaryPureCodeEnd 1 w) = ternaryConstants.mkQ w
    rw [map_one]; rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := Submodule.Quotient.mk_surjective ternaryConstants v
    change ternaryConstants.mkQ (ternaryPureCodeEnd (g*h) w) =
      ternaryConstants.mkQ (ternaryPureCodeEnd g (ternaryPureCodeEnd h w))
    rw [map_mul]; rfl

def ternaryPurePhaseLinear (g : TernaryPureAutomorphism) :
    TernaryPhaseModule ≃ₗ[ZMod 3] TernaryPhaseModule :=
  LinearEquiv.ofLinearMap (ternaryPurePhaseEndHom g) (ternaryPurePhaseEndHom g⁻¹)
    (by change ternaryPurePhaseEndHom g * ternaryPurePhaseEndHom g⁻¹ = 1
        rw [← map_mul, mul_inv_cancel, map_one])
    (by change ternaryPurePhaseEndHom g⁻¹ * ternaryPurePhaseEndHom g = 1
        rw [← map_mul, inv_mul_cancel, map_one])

def ternaryPurePhaseLinearHom : TernaryPureAutomorphism →*
    (TernaryPhaseModule ≃ₗ[ZMod 3] TernaryPhaseModule) where
  toFun := ternaryPurePhaseLinear
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun s : Module.End (ZMod 3) TernaryPhaseModule => s v)
      (map_one ternaryPurePhaseEndHom)
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun s : Module.End (ZMod 3) TernaryPhaseModule => s v)
      (map_mul ternaryPurePhaseEndHom g h)

theorem ternaryPurePhaseLinearHom_injective : Function.Injective ternaryPurePhaseLinearHom := by
  letI := ternaryPureAutomorphism_simple
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (inferInstance : ternaryPurePhaseLinearHom.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · obtain ⟨g,_,hfix⟩ := ternaryPhase_exists_fixed_free_operator
    have hg : ternaryPurePhaseLinearHom g = 1 := by
      change g ∈ ternaryPurePhaseLinearHom.ker
      rw [h]; trivial
    letI : Nontrivial TernaryPhaseModule :=
      Module.nontrivial_of_finrank_pos (R := ZMod 3) (by rw [ternaryPhaseModule_finrank]; decide)
    obtain ⟨v,hv⟩ := exists_ne (0 : TernaryPhaseModule)
    have he : ternaryPurePhaseEnd g v = v :=
      congrArg (fun e : TernaryPhaseModule ≃ₗ[ZMod 3] TernaryPhaseModule => e v) hg
    exact False.elim (hv (hfix v he))

theorem ternaryPureAutomorphism_noncommuting :
    ∃ g h : TernaryPureAutomorphism, g*h ≠ h*g := by
  obtain ⟨g,h,hne⟩ := mathieu11_noncommuting_pair
    (dodecadComplement ternaryComparisonDodecad) ternaryComplementPoint
  refine ⟨ternaryPureMathieu11Equiv g, ternaryPureMathieu11Equiv h, ?_⟩
  intro he
  apply hne
  apply ternaryPureMathieu11Equiv.injective
  simpa only [map_mul] using he

theorem ternaryPureAutomorphism_perfect : Group.IsPerfect TernaryPureAutomorphism := by
  letI := ternaryPureAutomorphism_simple
  exact Atlas.GroupTheory.nonabelian_simple_perfect _ ternaryPureAutomorphism_noncommuting

end Atlas.Codes

import Atlas.Conway.EisensteinHeavyUnitOrbit

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices MulAction

/-- The coordinate-permutation projection of the actual full local group. -/
def eisensteinLocalCoordinateProjection :
    eisensteinCoordinateFrameStabilizer →* TernaryPureAutomorphism :=
  (SemidirectProduct.rightHom (φ := eisensteinCodeActionHom)).comp
    ((MonoidHom.snd (Multiplicative (ZMod 2)) EisensteinCodeSemidirect).comp
      eisensteinFullFrameGroupEquiv.symm.toMonoidHom)

/-- Signs together with all code phases form a normal subgroup of the full
local group. The sign factor acts trivially on frames. -/
def eisensteinLocalSignedPhases : Subgroup eisensteinCoordinateFrameStabilizer :=
  eisensteinLocalCoordinateProjection.ker

instance eisensteinLocalSignedPhases_normal : eisensteinLocalSignedPhases.Normal :=
  inferInstanceAs eisensteinLocalCoordinateProjection.ker.Normal

local instance eisensteinSignedPhaseFrameAction : MulAction (Multiplicative ternaryGolay)
    EisensteinFrame := MulAction.compHom EisensteinFrame eisensteinPhaseIsometries

theorem eisensteinLocalSignedPhases_orbit (F : EisensteinFrame) :
    orbit eisensteinLocalSignedPhases F = orbit (Multiplicative ternaryGolay) F := by
  ext X
  constructor
  · rintro ⟨g,rfl⟩
    let p := eisensteinFullFrameGroupEquiv.symm g.val
    have hp : p.2.right=1 := g.property
    have he : eisensteinFrameAbstractHom p=g.val.val :=
      congrArg Subtype.val (eisensteinFullFrameGroupEquiv.apply_symm_apply g.val)
    refine ⟨p.2.left,?_⟩
    change eisensteinPhaseIsometries p.2.left • F = g.val.val • F
    rw [← he]
    change eisensteinPhaseIsometries p.2.left • F =
      (eisensteinSignHom p.1 * eisensteinCodeSemidirectIsometries p.2) • F
    rw [mul_smul]
    change eisensteinPhaseIsometries p.2.left • F =
      eisensteinSignHom p.1 • ((eisensteinPhaseIsometries p.2.left *
        eisensteinCoordinateIsometries p.2.right) • F)
    rw [hp,map_one,mul_one]
    by_cases h : p.1.toAdd=0 <;> simp [eisensteinSignHom,h,eisensteinSignIsometry_frame]
  · rintro ⟨t,rfl⟩
    let p : EisensteinFrameAbstractGroup := (1,⟨t,1⟩)
    let n := eisensteinFullFrameGroupEquiv p
    have hn : n ∈ eisensteinLocalSignedPhases := by
      change (eisensteinFullFrameGroupEquiv.symm n).2.right=1
      rw [eisensteinFullFrameGroupEquiv.symm_apply_apply]
    refine ⟨⟨n,hn⟩,?_⟩
    change eisensteinFrameAbstractHom p • F = eisensteinPhaseIsometries t • F
    change (eisensteinSignHom 1 * (eisensteinPhaseIsometries t *
      eisensteinCoordinateIsometries 1)) • F = _
    rw [map_one,map_one,mul_one,one_mul]

end Atlas.Conway

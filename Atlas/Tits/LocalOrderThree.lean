import Atlas.Tits.NormalQuotients

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem localOriginalD_pow_twelve : coupleOriginalD ^ 12 = 1 := by
  ext z
  all_goals decide +kernel +revert

theorem localCodeD_pow_twelve : coupleCodeD ^ 12 = 1 := by
  apply Subtype.ext
  change coupleCodeD.val ^ 12 = 1
  rw [coupleCodeD_transport, ← map_pow, localOriginalD_pow_twelve, map_one]

theorem localCodeD_fixes_reference : coupleCodeD ∈ codeReferenceStabilizer := by
  apply original_coordinate_cross_fix coupleCodeD coupleOriginalD coupleCodeD_transport
  decide +kernel

noncomputable def localD : Ambient := codePointHom ⟨coupleCodeD, localCodeD_fixes_reference⟩
noncomputable def localN : Ambient := localD ^ 4

theorem localN_cube : localN ^ 3 = 1 := by
  change (codePointHom ⟨coupleCodeD, localCodeD_fixes_reference⟩ ^ 4) ^ 3 = 1
  rw [← pow_mul, ← map_pow]
  have h : (⟨coupleCodeD, localCodeD_fixes_reference⟩ : codeReferenceStabilizer) ^ (4*3) = 1 :=
    Subtype.ext localCodeD_pow_twelve
  rw [h, map_one]

/-- The order-three element driving the local normal closure vanishes in each
nontrivial normal quotient of the actual cross stabilizer. -/
theorem localN_mem_normal (N : Subgroup Ambient) [N.Normal] (hN : N ≠ ⊥) : localN ∈ N :=
  cube_eq_one_mem_normal N hN localN localN_cube

end Atlas.Tits

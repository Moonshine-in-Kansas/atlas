import Atlas.LinearGroups.ReeF4.SpecialAdjoint
import Atlas.LinearGroups.ReeF4.SpecialSecondPivotVanishing
import Atlas.LinearGroups.ReeF4.WeylModel

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem special_suzuki_ovoid_raw_identity (x y : Fin 26 → F) (hx : x 9 = 0) :
    x 24*x 25*isotropyRawStar x y 25 + x 25^2*isotropyRawStar x y 16 +
      x 17*x 16*isotropyRawStar x y 25 + x 17^2*isotropyRawStar x y 17 =
    (x 23*x 25+x 15*x 17)*isotropyRawStar x y 9 +
      x 17*x 25*isotropyCross x y 9 +
      (x 25*y 17+x 17*y 25)*specialAdjoint9 x +
      x 25*y 9*specialAdjoint17 x + x 17*y 9*fullAdjointRoot25 x := by
  simp only [isotropyRawStar,isotropyCross,specialAdjoint9,specialAdjoint17,
    fullAdjointRoot25,Matrix.cons_val,hx,mul_zero,zero_mul,add_zero,zero_add]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem IsSpecialVector.suzuki_block_ovoid {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) {u : TraceZero K}
    (hu : IsSpecialVector m u) (hA4 : u.val.2 0 7 = 0) :
    u.val.2 2 6*u.val.2 2 7*theta K m (u.val.2 2 7) +
      (u.val.2 2 7)^2*theta K m (u.val.2 1 6) +
      u.val.2 1 7*u.val.2 1 6*theta K m (u.val.2 2 7) +
      (u.val.2 1 7)^2*theta K m (u.val.2 1 7) = 0 := by
  have ha := hu.specialAdjoint9_zero
  have hb := hu.specialAdjoint17_zero
  have hz : fullAdjointRoot25 (isotropyCoordinates u) = 0 := by
    rw [←fullAdjointRoot25_actual,hu.adjoint_zero]
    rfl
  obtain ⟨_,v,hd,he⟩ := hu
  have hr : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 9 = 0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 9]
    change theta K m (u.val.2 0 7) = 0
    rw [hA4,_root_.map_zero]
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v) 9 = 0 := by
    rw [←isotropyCross_actual,hd.2,_root_.map_zero]
    rfl
  have hi := special_suzuki_ovoid_raw_identity (isotropyCoordinates u)
    (isotropyCoordinates v) (show isotropyCoordinates u 9 = 0 from hA4)
  rw [fixedStar_coordinate_theta hcard u v hd he 25,
    fixedStar_coordinate_theta hcard u v hd he 16,
    fixedStar_coordinate_theta hcard u v hd he 17] at hi
  simp only [hr,hc,ha,hb,hz,mul_zero,add_zero] at hi
  exact hi

private theorem theta_ne_zero {m : ℕ} {a : K} (ha : a ≠ 0) : theta K m a ≠ 0 := by
  intro h
  apply ha
  apply (theta K m).injective
  simpa only [_root_.map_zero] using h

/-- If A4 and C4 vanish, the next root B4 is excluded by the actual special
condition, not by an asserted leading-root classification. -/
theorem IsSpecialVector.B4_zero_of_A4_C4_zero {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) {u : TraceZero K}
    (hu : IsSpecialVector m u) (hA4 : u.val.2 0 7 = 0)
    (hC4 : u.val.2 2 7 = 0) : u.val.2 1 7 = 0 := by
  have h := hu.suzuki_block_ovoid hcard hA4
  simp only [hC4,_root_.map_zero,zero_pow (by decide : 2 ≠ 0),
    mul_zero,zero_mul,zero_add] at h
  by_contra hd
  exact (mul_ne_zero (pow_ne_zero 2 hd) (theta_ne_zero hd)) h

/-- Applying the same structural equation to the actual Weyl reverse excludes
B3 as well. No point transitivity theorem is used. -/
theorem IsSpecialVector.B3_zero_of_A4_C4_zero {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) {u : TraceZero K}
    (hu : IsSpecialVector m u) (hA4 : u.val.2 0 7 = 0)
    (hC4 : u.val.2 2 7 = 0) : u.val.2 1 6 = 0 := by
  have hB4 := hu.B4_zero_of_A4_C4_zero hcard hA4 hC4
  let g : Model K m := ⟨weylRho,weylOperator_mem_modelSubgroup m 0⟩
  have hv := hu.map_model g
  have htop : (g.val u).val.2 0 7 = 0 := hA4
  have h := hv.suzuki_block_ovoid hcard htop
  change u.val.2 2 7*u.val.2 2 6*theta K m (u.val.2 2 6) +
    (u.val.2 2 6)^2*theta K m (u.val.2 1 7) +
    u.val.2 1 6*u.val.2 1 7*theta K m (u.val.2 2 6) +
    (u.val.2 1 6)^2*theta K m (u.val.2 1 6) = 0 at h
  simp only [hC4,hB4,_root_.map_zero,mul_zero,zero_mul,zero_add] at h
  by_contra he
  exact (mul_ne_zero (pow_ne_zero 2 he) (theta_ne_zero he)) h
end FiniteField
end Atlas.ReeF4

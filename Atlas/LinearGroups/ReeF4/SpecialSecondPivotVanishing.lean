import Atlas.LinearGroups.ReeF4.SpecialAdjointTop

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem special_reduced_suzuki_identity (x y : Fin 26 → F)
    (hx9 : x 9 = 0) (hx16 : x 16 = 0) (hx17 : x 17 = 0) :
    x 24*isotropyRawStar x y 25 =
      x 25*isotropyRawStar x y 16 + x 23*isotropyRawStar x y 9 +
      specialAdjoint9 x*y 17 + specialAdjoint17 x*y 9 := by
  simp only [isotropyRawStar,specialAdjoint9,specialAdjoint17,Matrix.cons_val,
    hx9,hx16,hx17,mul_zero,zero_mul,add_zero,zero_add]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- The scalar inverse twist converts the actual fixed-star equation to
ordinary bilinear coordinate equations. -/
theorem fixedStar_coordinate_theta {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) (u v : TraceZero K) (h : StarDomain u v)
    (he : u = proposedPartialProduct (thetaInv K m).toRingHom u v h) (k : Fin 26) :
    isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) k =
      theta K m (isotropyCoordinates u k) := by
  have hc := congrArg (isotropyCoordinates (F := K)) he
  change isotropyCoordinates u = isotropyCoordinates
    (traceZeroMap (thetaInv K m).toRingHom (proposedStarLinear (wedge u v))) at hc
  rw [isotropyCoordinates_map] at hc
  have hk := congrArg (fun x : K => theta K m x) (congrFun hc k)
  change theta K m (isotropyCoordinates u k) =
    theta K m (thetaInv K m
      (isotropyCoordinates (proposedStarLinear (wedge u v)) k)) at hk
  rw [theta_thetaInv hcard,isotropyRawStar_actual] at hk
  exact hk.symm

/-- The missing second-pivot coordinate vanishes intrinsically. This does not
assume a selected low-leading witness or the source's leading-product claim. -/
theorem IsSpecialVector.C3_zero_of_reduced_C4 {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) {u : TraceZero K}
    (hu : IsSpecialVector m u) (hA4 : u.val.2 0 7 = 0)
    (hB3 : u.val.2 1 6 = 0) (hB4 : u.val.2 1 7 = 0)
    (hC4 : u.val.2 2 7 ≠ 0) : u.val.2 2 6 = 0 := by
  have ha := hu.specialAdjoint9_zero
  have hb := hu.specialAdjoint17_zero
  obtain ⟨_,v,hd,he⟩ := hu
  have hid := special_reduced_suzuki_identity (isotropyCoordinates u) (isotropyCoordinates v)
    (show isotropyCoordinates u 9 = 0 from hA4)
    (show isotropyCoordinates u 16 = 0 from hB3)
    (show isotropyCoordinates u 17 = 0 from hB4)
  rw [fixedStar_coordinate_theta hcard u v hd he 25,
    fixedStar_coordinate_theta hcard u v hd he 16,
    fixedStar_coordinate_theta hcard u v hd he 9,ha,hb] at hid
  have h16 : isotropyCoordinates u 16 = 0 := hB3
  have h9 : isotropyCoordinates u 9 = 0 := hA4
  simp only [h16,h9,_root_.map_zero,mul_zero,zero_mul,add_zero] at hid
  have hn : theta K m (isotropyCoordinates u 25) ≠ 0 := by
    intro hz
    apply hC4
    have hh : isotropyCoordinates u 25 = 0 :=
      (theta K m).injective (hz.trans (theta K m).map_zero.symm)
    exact hh
  exact (mul_eq_zero.mp hid).resolve_right hn
end FiniteField
end Atlas.ReeF4

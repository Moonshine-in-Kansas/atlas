import Atlas.LinearGroups.ReeF4.SpecialLeadingChecks.Row14

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def specialLeadingCertificate23 (x y : Fin 26 → F) : F := (fullAdjointRoot15 x) * (x 23 * y 8) + (fullAdjointRoot7 x) * (x 21 * y 17) + (fullAdjointRoot6 x) * (x 23 * y 17) + (isotropyRawStar x y 25) * (x 21 * x 22) + (isotropyRawStar x y 25) * (x 20 * x 23) + (isotropyRawStar x y 25) * (x 13 * x 14) + (isotropyRawStar x y 25) * (x 4 * x 7) + (isotropyRawStar x y 25) * (x 1 * x 1) + (isotropyRawStar x y 25) * (x 0 * x 1) + (isotropyRawStar x y 24) * (x 7 * x 7) + (isotropyRawStar x y 17) * (x 5 * x 7) + (isotropyRawStar x y 16) * (x 6 * x 7) + (isotropyRawStar x y 15) * (x 21 * x 23) + (isotropyCross x y 25) * (x 7 * x 14) + (isotropyCross x y 25) * (x 1 * x 23) + (isotropyCross x y 17) * (x 7 * x 21) + (isotropyCross x y 16) * (x 7 * x 23) + (isotropyCross x y 9) * (x 13 * x 23) + (isotropyCross x y 9) * (x 1 * x 7) + (isotropyCross x y 9) * (x 0 * x 7)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem specialLeadingIdentity23 (x y : Fin 26 → F)
    (hz : ∀ j, specialAbsoluteGrade 23 < specialAbsoluteGrade j → x j=0) :
    x 23^2*isotropyRawStar x y 23=specialLeadingCertificate23 x y := by
  have hz8 : x 8=0 := hz 8 (by decide)
  have hz9 : x 9=0 := hz 9 (by decide)
  have hz15 : x 15=0 := hz 15 (by decide)
  have hz16 : x 16=0 := hz 16 (by decide)
  have hz17 : x 17=0 := hz 17 (by decide)
  have hz24 : x 24=0 := hz 24 (by decide)
  have hz25 : x 25=0 := hz 25 (by decide)
  simp only [specialLeadingCertificate23,isotropyRawStar,isotropyCross,isotropyPolar,fullAdjointRoot15,fullAdjointRoot7,fullAdjointRoot6,Matrix.cons_val,hz8,hz9,hz15,hz16,hz17,hz24,hz25,mul_zero,zero_mul,add_zero,zero_add]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
theorem IsSpecialVector.forbidden_leading_coordinate23 {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) {u : TraceZero K}
    (hu : IsSpecialVector m u)
    (hz : ∀ j, specialAbsoluteGrade 23 < specialAbsoluteGrade j → isotropyCoordinates u j=0) :
    isotropyCoordinates u 23=0 := by
  have hadj := hu.adjoint_zero
  have haroot15 : fullAdjointRoot15 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot15_actual,hadj]
    rfl
  have haroot7 : fullAdjointRoot7 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot7_actual,hadj]
    rfl
  have haroot6 : fullAdjointRoot6 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot6_actual,hadj]
    rfl
  obtain ⟨_,v,hd,he⟩ := hu
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,hd.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,hd.1]
  have hr25 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 25=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 25,hz 25 (by decide),_root_.map_zero]
  have hr24 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 24=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 24,hz 24 (by decide),_root_.map_zero]
  have hr17 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 17=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 17,hz 17 (by decide),_root_.map_zero]
  have hr16 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 16=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 16,hz 16 (by decide),_root_.map_zero]
  have hr15 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 15=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 15,hz 15 (by decide),_root_.map_zero]
  have hi := specialLeadingIdentity23 (isotropyCoordinates u) (isotropyCoordinates v) hz
  simp only [specialLeadingCertificate23,hc,hp,hr25,hr24,hr17,hr16,hr15,haroot15,haroot7,haroot6,Pi.zero_apply,mul_zero,zero_mul,add_zero,zero_add] at hi
  rw [fixedStar_coordinate_theta hcard u v hd he 23] at hi
  by_contra hn
  have ht : theta K m (isotropyCoordinates u 23) ≠ 0 := by
    intro h
    apply hn
    apply (theta K m).injective
    simpa only [_root_.map_zero] using h
  exact (mul_ne_zero (pow_ne_zero 2 hn) ht) hi
end FiniteField
end Atlas.ReeF4

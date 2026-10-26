import Atlas.LinearGroups.ReeF4.SpecialLeadingChecks.Row01

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def specialLeadingCertificate6 (x y : Fin 26 → F) : F := (fullAdjointRoot13 x) * (x 0 * y 15) + (fullAdjointRoot13 x) * (x 19 * y 9) + (fullAdjointRoot11 x) * (x 6 * y 25) + (fullAdjointRoot6 x) * (x 19 * y 17) + (fullAdjointRoot6 x) * (x 22 * y 15) + (fullAdjointRoot6 x) * (x 1 * y 7) + (fullAdjointRoot3 x) * (x 13 * y 25) + (isotropyRawStar x y 8) * (x 13 * x 13) + (isotropyRawStar x y 7) * (x 13 * x 14) + (isotropyRawStar x y 7) * (x 5 * x 6) + (isotropyCross x y 25) * (x 6 * x 11) + (isotropyCross x y 25) * (x 3 * x 13) + (isotropyCross x y 23) * (x 6 * x 13) + (isotropyCross x y 15) * (x 6 * x 22) + (isotropyCross x y 15) * (x 0 * x 13) + (isotropyCross x y 7) * (x 1 * x 6)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem specialLeadingIdentity6 (x y : Fin 26 → F)
    (hz : ∀ j, specialAbsoluteGrade 6 < specialAbsoluteGrade j → x j=0) :
    x 6^2*isotropyRawStar x y 6=specialLeadingCertificate6 x y := by
  have hz7 : x 7=0 := hz 7 (by decide)
  have hz8 : x 8=0 := hz 8 (by decide)
  have hz9 : x 9=0 := hz 9 (by decide)
  have hz15 : x 15=0 := hz 15 (by decide)
  have hz16 : x 16=0 := hz 16 (by decide)
  have hz17 : x 17=0 := hz 17 (by decide)
  have hz21 : x 21=0 := hz 21 (by decide)
  have hz23 : x 23=0 := hz 23 (by decide)
  have hz24 : x 24=0 := hz 24 (by decide)
  have hz25 : x 25=0 := hz 25 (by decide)
  simp only [specialLeadingCertificate6,isotropyRawStar,isotropyCross,isotropyPolar,fullAdjointRoot13,fullAdjointRoot11,fullAdjointRoot6,fullAdjointRoot3,Matrix.cons_val,hz7,hz8,hz9,hz15,hz16,hz17,hz21,hz23,hz24,hz25,mul_zero,zero_mul,add_zero,zero_add]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
theorem IsSpecialVector.forbidden_leading_coordinate6 {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) {u : TraceZero K}
    (hu : IsSpecialVector m u)
    (hz : ∀ j, specialAbsoluteGrade 6 < specialAbsoluteGrade j → isotropyCoordinates u j=0) :
    isotropyCoordinates u 6=0 := by
  have hadj := hu.adjoint_zero
  have haroot13 : fullAdjointRoot13 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot13_actual,hadj]
    rfl
  have haroot11 : fullAdjointRoot11 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot11_actual,hadj]
    rfl
  have haroot6 : fullAdjointRoot6 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot6_actual,hadj]
    rfl
  have haroot3 : fullAdjointRoot3 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot3_actual,hadj]
    rfl
  obtain ⟨_,v,hd,he⟩ := hu
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,hd.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,hd.1]
  have hr8 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 8=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 8,hz 8 (by decide),_root_.map_zero]
  have hr7 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 7=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 7,hz 7 (by decide),_root_.map_zero]
  have hi := specialLeadingIdentity6 (isotropyCoordinates u) (isotropyCoordinates v) hz
  simp only [specialLeadingCertificate6,hc,hp,hr8,hr7,haroot13,haroot11,haroot6,haroot3,Pi.zero_apply,mul_zero,zero_mul,add_zero,zero_add] at hi
  rw [fixedStar_coordinate_theta hcard u v hd he 6] at hi
  by_contra hn
  have ht : theta K m (isotropyCoordinates u 6) ≠ 0 := by
    intro h
    apply hn
    apply (theta K m).injective
    simpa only [_root_.map_zero] using h
  exact (mul_ne_zero (pow_ne_zero 2 hn) ht) hi
end FiniteField
end Atlas.ReeF4

import Atlas.LinearGroups.ReeF4.SpecialLeadingChecks.Row12

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def specialLeadingCertificate21 (x y : Fin 26 → F) : F := (fullAdjointRoot21 x) * (x 12 * y 9) + (fullAdjointRoot21 x) * (x 14 * y 8) + (fullAdjointRoot14 x) * (x 20 * y 9) + (fullAdjointRoot14 x) * (x 21 * y 8) + (fullAdjointRoot4 x) * (x 21 * y 17) + (fullAdjointRoot4 x) * (x 1 * y 9) + (fullAdjointRoot4 x) * (x 0 * y 9) + (isotropyRawStar x y 24) * (x 21 * x 22) + (isotropyRawStar x y 24) * (x 13 * x 14) + (isotropyRawStar x y 23) * (x 14 * x 14) + (isotropyRawStar x y 17) * (x 12 * x 14) + (isotropyRawStar x y 17) * (x 4 * x 5) + (isotropyRawStar x y 16) * (x 20 * x 21) + (isotropyRawStar x y 16) * (x 4 * x 6) + (isotropyCross x y 25) * (x 4 * x 14) + (isotropyCross x y 17) * (x 4 * x 21) + (isotropyCross x y 9) * (x 14 * x 20) + (isotropyCross x y 9) * (x 1 * x 4) + (isotropyCross x y 9) * (x 0 * x 4) + (isotropyCross x y 8) * (x 14 * x 21)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem specialLeadingIdentity21 (x y : Fin 26 → F)
    (hz : ∀ j, specialAbsoluteGrade 21 < specialAbsoluteGrade j → x j=0) :
    x 21^2*isotropyRawStar x y 21=specialLeadingCertificate21 x y := by
  have hz7 : x 7=0 := hz 7 (by decide)
  have hz8 : x 8=0 := hz 8 (by decide)
  have hz9 : x 9=0 := hz 9 (by decide)
  have hz15 : x 15=0 := hz 15 (by decide)
  have hz16 : x 16=0 := hz 16 (by decide)
  have hz17 : x 17=0 := hz 17 (by decide)
  have hz23 : x 23=0 := hz 23 (by decide)
  have hz24 : x 24=0 := hz 24 (by decide)
  have hz25 : x 25=0 := hz 25 (by decide)
  simp only [specialLeadingCertificate21,isotropyRawStar,isotropyCross,isotropyPolar,fullAdjointRoot21,fullAdjointRoot14,fullAdjointRoot4,Matrix.cons_val,hz7,hz8,hz9,hz15,hz16,hz17,hz23,hz24,hz25,mul_zero,zero_mul,add_zero,zero_add]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
theorem IsSpecialVector.forbidden_leading_coordinate21 {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) {u : TraceZero K}
    (hu : IsSpecialVector m u)
    (hz : ∀ j, specialAbsoluteGrade 21 < specialAbsoluteGrade j → isotropyCoordinates u j=0) :
    isotropyCoordinates u 21=0 := by
  have hadj := hu.adjoint_zero
  have haroot21 : fullAdjointRoot21 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot21_actual,hadj]
    rfl
  have haroot14 : fullAdjointRoot14 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot14_actual,hadj]
    rfl
  have haroot4 : fullAdjointRoot4 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot4_actual,hadj]
    rfl
  obtain ⟨_,v,hd,he⟩ := hu
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,hd.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,hd.1]
  have hr24 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 24=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 24,hz 24 (by decide),_root_.map_zero]
  have hr23 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 23=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 23,hz 23 (by decide),_root_.map_zero]
  have hr17 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 17=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 17,hz 17 (by decide),_root_.map_zero]
  have hr16 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 16=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 16,hz 16 (by decide),_root_.map_zero]
  have hi := specialLeadingIdentity21 (isotropyCoordinates u) (isotropyCoordinates v) hz
  simp only [specialLeadingCertificate21,hc,hp,hr24,hr23,hr17,hr16,haroot21,haroot14,haroot4,Pi.zero_apply,mul_zero,zero_mul,add_zero,zero_add] at hi
  rw [fixedStar_coordinate_theta hcard u v hd he 21] at hi
  by_contra hn
  have ht : theta K m (isotropyCoordinates u 21) ≠ 0 := by
    intro h
    apply hn
    apply (theta K m).injective
    simpa only [_root_.map_zero] using h
  exact (mul_ne_zero (pow_ne_zero 2 hn) ht) hi
end FiniteField
end Atlas.ReeF4

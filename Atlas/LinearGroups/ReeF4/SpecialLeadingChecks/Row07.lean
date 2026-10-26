import Atlas.LinearGroups.ReeF4.SpecialLeadingChecks.Row06

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def specialLeadingCertificate13 (x y : Fin 26 → F) : F := (fullAdjointRoot19 x) * (x 13 * y 7) + (isotropyRawStar x y 15) * (x 19 * x 19) + (isotropyRawStar x y 7) * (x 19 * x 22) + (isotropyRawStar x y 7) * (x 11 * x 13) + (isotropyCross x y 7) * (x 13 * x 19)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem specialLeadingIdentity13 (x y : Fin 26 → F)
    (hz : ∀ j, specialAbsoluteGrade 13 < specialAbsoluteGrade j → x j=0) :
    x 13^2*isotropyRawStar x y 13=specialLeadingCertificate13 x y := by
  have hz0 : x 0=0 := hz 0 (by decide)
  have hz1 : x 1=0 := hz 1 (by decide)
  have hz6 : x 6=0 := hz 6 (by decide)
  have hz7 : x 7=0 := hz 7 (by decide)
  have hz8 : x 8=0 := hz 8 (by decide)
  have hz9 : x 9=0 := hz 9 (by decide)
  have hz14 : x 14=0 := hz 14 (by decide)
  have hz15 : x 15=0 := hz 15 (by decide)
  have hz16 : x 16=0 := hz 16 (by decide)
  have hz17 : x 17=0 := hz 17 (by decide)
  have hz21 : x 21=0 := hz 21 (by decide)
  have hz23 : x 23=0 := hz 23 (by decide)
  have hz24 : x 24=0 := hz 24 (by decide)
  have hz25 : x 25=0 := hz 25 (by decide)
  simp only [specialLeadingCertificate13,isotropyRawStar,isotropyCross,isotropyPolar,fullAdjointRoot19,Matrix.cons_val,hz0,hz1,hz6,hz7,hz8,hz9,hz14,hz15,hz16,hz17,hz21,hz23,hz24,hz25,mul_zero,zero_mul,add_zero,zero_add]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
theorem IsSpecialVector.forbidden_leading_coordinate13 {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) {u : TraceZero K}
    (hu : IsSpecialVector m u)
    (hz : ∀ j, specialAbsoluteGrade 13 < specialAbsoluteGrade j → isotropyCoordinates u j=0) :
    isotropyCoordinates u 13=0 := by
  have hadj := hu.adjoint_zero
  have haroot19 : fullAdjointRoot19 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot19_actual,hadj]
    rfl
  obtain ⟨_,v,hd,he⟩ := hu
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,hd.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,hd.1]
  have hr15 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 15=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 15,hz 15 (by decide),_root_.map_zero]
  have hr7 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 7=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 7,hz 7 (by decide),_root_.map_zero]
  have hi := specialLeadingIdentity13 (isotropyCoordinates u) (isotropyCoordinates v) hz
  simp only [specialLeadingCertificate13,hc,hp,hr15,hr7,haroot19,Pi.zero_apply,mul_zero,zero_mul,add_zero,zero_add] at hi
  rw [fixedStar_coordinate_theta hcard u v hd he 13] at hi
  by_contra hn
  have ht : theta K m (isotropyCoordinates u 13) ≠ 0 := by
    intro h
    apply hn
    apply (theta K m).injective
    simpa only [_root_.map_zero] using h
  exact (mul_ne_zero (pow_ne_zero 2 hn) ht) hi
end FiniteField
end Atlas.ReeF4

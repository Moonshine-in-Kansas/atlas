import Atlas.LinearGroups.ReeF4.SpecialLeadingChecks.Row00

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def specialLeadingCertificate5 (x y : Fin 26 → F) : F := (isotropyRawStar x y 14) * (x 3 * x 5) + (isotropyRawStar x y 1) * (x 4 * x 5) + (isotropyRawStar x y 0) * (x 4 * x 5) + (isotropyCross x y 24) * (x 5 * x 10) + (isotropyCross x y 21) * (x 5 * x 12) + (isotropyCross x y 16) * (x 5 * x 18) + (isotropyCross x y 14) * (x 5 * x 20) + (isotropyCross x y 1) * (x 4 * x 5)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem specialLeadingIdentity5 (x y : Fin 26 → F)
    (hz : ∀ j, specialAbsoluteGrade 5 < specialAbsoluteGrade j → x j=0) :
    x 5^2*isotropyRawStar x y 5=specialLeadingCertificate5 x y := by
  have hz0 : x 0=0 := hz 0 (by decide)
  have hz1 : x 1=0 := hz 1 (by decide)
  have hz6 : x 6=0 := hz 6 (by decide)
  have hz7 : x 7=0 := hz 7 (by decide)
  have hz8 : x 8=0 := hz 8 (by decide)
  have hz9 : x 9=0 := hz 9 (by decide)
  have hz13 : x 13=0 := hz 13 (by decide)
  have hz14 : x 14=0 := hz 14 (by decide)
  have hz15 : x 15=0 := hz 15 (by decide)
  have hz16 : x 16=0 := hz 16 (by decide)
  have hz17 : x 17=0 := hz 17 (by decide)
  have hz21 : x 21=0 := hz 21 (by decide)
  have hz23 : x 23=0 := hz 23 (by decide)
  have hz24 : x 24=0 := hz 24 (by decide)
  have hz25 : x 25=0 := hz 25 (by decide)
  simp only [specialLeadingCertificate5,isotropyRawStar,isotropyCross,isotropyPolar,Matrix.cons_val,hz0,hz1,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz23,hz24,hz25,mul_zero,zero_mul,add_zero,zero_add]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
theorem IsSpecialVector.forbidden_leading_coordinate5 {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) {u : TraceZero K}
    (hu : IsSpecialVector m u)
    (hz : ∀ j, specialAbsoluteGrade 5 < specialAbsoluteGrade j → isotropyCoordinates u j=0) :
    isotropyCoordinates u 5=0 := by
  have hadj := hu.adjoint_zero
  obtain ⟨_,v,hd,he⟩ := hu
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,hd.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,hd.1]
  have hr14 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 14=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 14,hz 14 (by decide),_root_.map_zero]
  have hr1 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 1=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 1,hz 1 (by decide),_root_.map_zero]
  have hr0 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 0=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 0,hz 0 (by decide),_root_.map_zero]
  have hi := specialLeadingIdentity5 (isotropyCoordinates u) (isotropyCoordinates v) hz
  simp only [specialLeadingCertificate5,hc,hp,hr14,hr1,hr0,Pi.zero_apply,mul_zero,zero_mul,add_zero,zero_add] at hi
  rw [fixedStar_coordinate_theta hcard u v hd he 5] at hi
  by_contra hn
  have ht : theta K m (isotropyCoordinates u 5) ≠ 0 := by
    intro h
    apply hn
    apply (theta K m).injective
    simpa only [_root_.map_zero] using h
  exact (mul_ne_zero (pow_ne_zero 2 hn) ht) hi
end FiniteField
end Atlas.ReeF4

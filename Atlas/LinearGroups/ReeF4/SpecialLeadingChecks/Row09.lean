import Atlas.LinearGroups.ReeF4.SpecialLeadingChecks.Row08

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def specialLeadingCertificate15 (x y : Fin 26 → F) : F := (fullAdjointRoot25 x) * (x 7 * y 15) + (fullAdjointRoot25 x) * (x 15 * y 7) + (fullAdjointRoot15 x) * (x 7 * y 25) + (fullAdjointRoot7 x) * (x 15 * y 25) + (isotropyRawStar x y 25) * (x 13 * x 15) + (isotropyRawStar x y 25) * (x 6 * x 7) + (isotropyRawStar x y 17) * (x 7 * x 7) + (isotropyCross x y 25) * (x 7 * x 15)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem specialLeadingIdentity15 (x y : Fin 26 → F)
    (hz : ∀ j, specialAbsoluteGrade 15 < specialAbsoluteGrade j → x j=0) :
    x 15^2*isotropyRawStar x y 15=specialLeadingCertificate15 x y := by
  have hz9 : x 9=0 := hz 9 (by decide)
  have hz16 : x 16=0 := hz 16 (by decide)
  have hz17 : x 17=0 := hz 17 (by decide)
  have hz24 : x 24=0 := hz 24 (by decide)
  have hz25 : x 25=0 := hz 25 (by decide)
  simp only [specialLeadingCertificate15,isotropyRawStar,isotropyCross,isotropyPolar,fullAdjointRoot25,fullAdjointRoot15,fullAdjointRoot7,Matrix.cons_val,hz9,hz16,hz17,hz24,hz25,mul_zero,zero_mul,add_zero,zero_add]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
theorem IsSpecialVector.forbidden_leading_coordinate15 {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) {u : TraceZero K}
    (hu : IsSpecialVector m u)
    (hz : ∀ j, specialAbsoluteGrade 15 < specialAbsoluteGrade j → isotropyCoordinates u j=0) :
    isotropyCoordinates u 15=0 := by
  have hadj := hu.adjoint_zero
  have haroot25 : fullAdjointRoot25 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot25_actual,hadj]
    rfl
  have haroot15 : fullAdjointRoot15 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot15_actual,hadj]
    rfl
  have haroot7 : fullAdjointRoot7 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot7_actual,hadj]
    rfl
  obtain ⟨_,v,hd,he⟩ := hu
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,hd.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,hd.1]
  have hr25 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 25=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 25,hz 25 (by decide),_root_.map_zero]
  have hr17 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 17=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 17,hz 17 (by decide),_root_.map_zero]
  have hi := specialLeadingIdentity15 (isotropyCoordinates u) (isotropyCoordinates v) hz
  simp only [specialLeadingCertificate15,hc,hp,hr25,hr17,haroot25,haroot15,haroot7,Pi.zero_apply,mul_zero,zero_mul,add_zero,zero_add] at hi
  rw [fixedStar_coordinate_theta hcard u v hd he 15] at hi
  by_contra hn
  have ht : theta K m (isotropyCoordinates u 15) ≠ 0 := by
    intro h
    apply hn
    apply (theta K m).injective
    simpa only [_root_.map_zero] using h
  exact (mul_ne_zero (pow_ne_zero 2 hn) ht) hi
end FiniteField
end Atlas.ReeF4

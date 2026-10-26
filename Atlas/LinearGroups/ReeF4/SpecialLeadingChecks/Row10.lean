import Atlas.LinearGroups.ReeF4.SpecialLeadingChecks.Row09

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def specialLeadingCertificate16 (x y : Fin 26 → F) : F := (fullAdjointRoot24 x) * (x 16 * y 9) + (fullAdjointRoot16 x) * (x 24 * y 9) + (specialAdjoint9 x) * (x 16 * y 24) + (specialAdjoint9 x) * (x 24 * y 16) + (isotropyRawStar x y 17) * (x 24 * x 24) + (isotropyRawStar x y 9) * (x 21 * x 24) + (isotropyRawStar x y 9) * (x 14 * x 16) + (isotropyCross x y 9) * (x 16 * x 24)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem specialLeadingIdentity16 (x y : Fin 26 → F)
    (hz : ∀ j, specialAbsoluteGrade 16 < specialAbsoluteGrade j → x j=0) :
    x 16^2*isotropyRawStar x y 16=specialLeadingCertificate16 x y := by
  have hz9 : x 9=0 := hz 9 (by decide)
  have hz17 : x 17=0 := hz 17 (by decide)
  have hz25 : x 25=0 := hz 25 (by decide)
  simp only [specialLeadingCertificate16,isotropyRawStar,isotropyCross,isotropyPolar,fullAdjointRoot24,fullAdjointRoot16,specialAdjoint9,Matrix.cons_val,hz9,hz17,hz25,mul_zero,zero_mul,add_zero,zero_add]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
theorem IsSpecialVector.forbidden_leading_coordinate16 {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) {u : TraceZero K}
    (hu : IsSpecialVector m u)
    (hz : ∀ j, specialAbsoluteGrade 16 < specialAbsoluteGrade j → isotropyCoordinates u j=0) :
    isotropyCoordinates u 16=0 := by
  have hadj := hu.adjoint_zero
  have haroot24 : fullAdjointRoot24 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot24_actual,hadj]
    rfl
  have haroot16 : fullAdjointRoot16 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot16_actual,hadj]
    rfl
  have haroot9 : specialAdjoint9 (isotropyCoordinates u)=0 := by
    rw [←specialAdjoint9_actual,hadj]
    rfl
  obtain ⟨_,v,hd,he⟩ := hu
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,hd.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,hd.1]
  have hr17 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 17=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 17,hz 17 (by decide),_root_.map_zero]
  have hr9 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 9=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 9,hz 9 (by decide),_root_.map_zero]
  have hi := specialLeadingIdentity16 (isotropyCoordinates u) (isotropyCoordinates v) hz
  simp only [specialLeadingCertificate16,hc,hp,hr17,hr9,haroot24,haroot16,haroot9,Pi.zero_apply,mul_zero,zero_mul,add_zero,zero_add] at hi
  rw [fixedStar_coordinate_theta hcard u v hd he 16] at hi
  by_contra hn
  have ht : theta K m (isotropyCoordinates u 16) ≠ 0 := by
    intro h
    apply hn
    apply (theta K m).injective
    simpa only [_root_.map_zero] using h
  exact (mul_ne_zero (pow_ne_zero 2 hn) ht) hi
end FiniteField
end Atlas.ReeF4

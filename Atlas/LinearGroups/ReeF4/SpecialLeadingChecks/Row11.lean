import Atlas.LinearGroups.ReeF4.SpecialLeadingChecks.Row10

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def specialLeadingCertificate17 (x y : Fin 26 → F) : F := (fullAdjointRoot25 x) * (x 17 * y 9) + (specialAdjoint9 x) * (x 17 * y 25) + (isotropyRawStar x y 25) * (x 16 * x 17) + (isotropyRawStar x y 9) * (x 15 * x 17)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem specialLeadingIdentity17 (x y : Fin 26 → F)
    (hz : ∀ j, specialAbsoluteGrade 17 < specialAbsoluteGrade j → x j=0) :
    x 17^2*isotropyRawStar x y 17=specialLeadingCertificate17 x y := by
  have hz9 : x 9=0 := hz 9 (by decide)
  have hz25 : x 25=0 := hz 25 (by decide)
  simp only [specialLeadingCertificate17,isotropyRawStar,isotropyCross,isotropyPolar,fullAdjointRoot25,specialAdjoint9,Matrix.cons_val,hz9,hz25,mul_zero,zero_mul,add_zero,zero_add]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
theorem IsSpecialVector.forbidden_leading_coordinate17 {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) {u : TraceZero K}
    (hu : IsSpecialVector m u)
    (hz : ∀ j, specialAbsoluteGrade 17 < specialAbsoluteGrade j → isotropyCoordinates u j=0) :
    isotropyCoordinates u 17=0 := by
  have hadj := hu.adjoint_zero
  have haroot25 : fullAdjointRoot25 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointRoot25_actual,hadj]
    rfl
  have haroot9 : specialAdjoint9 (isotropyCoordinates u)=0 := by
    rw [←specialAdjoint9_actual,hadj]
    rfl
  obtain ⟨_,v,hd,he⟩ := hu
  have hc : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,hd.2,_root_.map_zero]
  have hp : isotropyPolar (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyPolar_actual,hd.1]
  have hr25 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 25=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 25,hz 25 (by decide),_root_.map_zero]
  have hr9 : isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) 9=0 := by
    rw [fixedStar_coordinate_theta hcard u v hd he 9,hz 9 (by decide),_root_.map_zero]
  have hi := specialLeadingIdentity17 (isotropyCoordinates u) (isotropyCoordinates v) hz
  simp only [specialLeadingCertificate17,hc,hp,hr25,hr9,haroot25,haroot9,Pi.zero_apply,mul_zero,zero_mul,add_zero,zero_add] at hi
  rw [fixedStar_coordinate_theta hcard u v hd he 17] at hi
  by_contra hn
  have ht : theta K m (isotropyCoordinates u 17) ≠ 0 := by
    intro h
    apply hn
    apply (theta K m).injective
    simpa only [_root_.map_zero] using h
  exact (mul_ne_zero (pow_ne_zero 2 hn) ht) hi
end FiniteField
end Atlas.ReeF4

import Atlas.LinearGroups.ReeF4.SpecialLeadingRootIdentities
import Atlas.LinearGroups.ReeF4.SpecialSuzukiOvoid

/-! Explicit upper-coordinate assumptions, no witness bound. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

private theorem leading_theta_ne_zero (m : ℕ) {a : K} (ha : a ≠ 0) :
    theta K m a ≠ 0 := by
  intro h
  apply ha
  apply (theta K m).injective
  simpa only [_root_.map_zero] using h

theorem IsSpecialVector.B2_zero_of_A4_C4_zero {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) {u : TraceZero K}
    (hu : IsSpecialVector m u) (hA4 : u.val.2 0 7 = 0)
    (hC4 : u.val.2 2 7 = 0) : u.val.2 1 5 = 0 := by
  let g : Model K m := ⟨weylSigma,weylOperator_mem_modelSubgroup m 1⟩
  have hv := hu.map_model g
  have htopA : (g.val u).val.2 0 7 = 0 := hC4
  have htopC : (g.val u).val.2 2 7 = 0 := hA4
  have h := hv.B3_zero_of_A4_C4_zero hcard htopA htopC
  change u.val.2 1 5 = 0 at h
  exact h

theorem IsSpecialVector.A3_zero_of_upper_zero {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) {u : TraceZero K}
    (hu : IsSpecialVector m u)
    (h9 : isotropyCoordinates u 9 = 0)
    (h15 : isotropyCoordinates u 15 = 0)
    (h16 : isotropyCoordinates u 16 = 0)
    (h17 : isotropyCoordinates u 17 = 0)
    (h24 : isotropyCoordinates u 24 = 0)
    (h25 : isotropyCoordinates u 25 = 0) : isotropyCoordinates u 8 = 0 := by
  have ha := hu.adjoint_zero
  have hz16 : fullAdjointRoot16 (isotropyCoordinates u) = 0 := by
    rw [←fullAdjointRoot16_actual,ha]
    rfl
  have hz17 := hu.specialAdjoint17_zero
  have hz24 : fullAdjointRoot24 (isotropyCoordinates u) = 0 := by
    rw [←fullAdjointRoot24_actual,ha]
    rfl
  obtain ⟨_,v,hd,he⟩ := hu
  have hi := leading8_raw_identity (isotropyCoordinates u) (isotropyCoordinates v)
    h9 h15 h16 h17 h24 h25
  simp only [fixedStar_coordinate_theta hcard u v hd he] at hi
  simp only [hz16,hz17,hz24,h9,_root_.map_zero,mul_zero,add_zero,zero_add,pow_one] at hi
  by_contra hn
  exact (mul_ne_zero hn (leading_theta_ne_zero m hn)) hi

theorem IsSpecialVector.C2_zero_of_upper_zero {m : ℕ}
    (hcard : Nat.card K = 2^(2*m+1)) {u : TraceZero K}
    (hu : IsSpecialVector m u)
    (h8 : isotropyCoordinates u 8 = 0)
    (h9 : isotropyCoordinates u 9 = 0)
    (h15 : isotropyCoordinates u 15 = 0)
    (h16 : isotropyCoordinates u 16 = 0)
    (h17 : isotropyCoordinates u 17 = 0)
    (h24 : isotropyCoordinates u 24 = 0)
    (h25 : isotropyCoordinates u 25 = 0) : isotropyCoordinates u 23 = 0 := by
  have ha := hu.adjoint_zero
  have hz6 : fullAdjointRoot6 (isotropyCoordinates u) = 0 := by
    rw [←fullAdjointRoot6_actual,ha]
    rfl
  have hz7 : fullAdjointRoot7 (isotropyCoordinates u) = 0 := by
    rw [←fullAdjointRoot7_actual,ha]
    rfl
  have hz14 : fullAdjointRoot14 (isotropyCoordinates u) = 0 := by
    rw [←fullAdjointRoot14_actual,ha]
    rfl
  have hz15 : fullAdjointRoot15 (isotropyCoordinates u) = 0 := by
    rw [←fullAdjointRoot15_actual,ha]
    rfl
  obtain ⟨_,v,hd,he⟩ := hu
  have hc (j : Fin 26) : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v) j = 0 := by
    rw [←isotropyCross_actual,hd.2,_root_.map_zero]
    rfl
  have hi := leading23_raw_identity (isotropyCoordinates u) (isotropyCoordinates v)
    h8 h9 h15 h16 h17 h24 h25
  simp only [fixedStar_coordinate_theta hcard u v hd he] at hi
  simp only [hz6,hz7,hz14,hz15,h15,h17,h25,_root_.map_zero,hc,mul_zero,add_zero,zero_add] at hi
  by_contra hn
  exact (mul_ne_zero (pow_ne_zero 2 hn) (leading_theta_ne_zero m hn)) hi

end Atlas.ReeF4

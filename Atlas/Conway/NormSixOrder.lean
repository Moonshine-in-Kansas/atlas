import Atlas.Conway.NormSixTransitivity

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem normSix_vector_orbit_stabilizer (x : LeechShell 6) :
    16773120 * Nat.card (fullVectorStabilizer x.val) = Nat.card LeechIsometryGroup := by
  letI := full_normSix_pretransitive
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup LeechIsometryGroup x)
  rw [Nat.card_prod,MulAction.orbit_eq_univ,Nat.card_congr (Equiv.Set.univ _),
    leech_six_shell_card,full_shell_stabilizer_eq] at h
  exact h

theorem normSix_vector_stabilizer_order (x : LeechShell 6) :
    Nat.card (fullVectorStabilizer x.val) = 495766656000 := by
  have h := normSix_vector_orbit_stabilizer x
  rw [leechIsometryGroup_order] at h
  omega

theorem normSix_vector_stabilizer_factorization (x : LeechShell 6) :
    Nat.card (fullVectorStabilizer x.val) = 2^10 * 3^7 * 5^3 * 7 * 11 * 23 := by
  rw [normSix_vector_stabilizer_order]
  norm_num

theorem normSix_vector_ne_zero (x : LeechShell 6) : x.val ≠ 0 := by
  intro h
  have hn := x.prop
  rw [h] at hn
  norm_num [integerDot] at hn

end Atlas.Conway

import Atlas.LinearGroups.Type3D4

noncomputable section
namespace Atlas.Triality

theorem order_q2 : Nat.card (PrimePowerModel 2 1) = 211341312 := by
  have h := primePower_order 2 1 (by omega)
  norm_num at h ⊢
  exact h

theorem simple_q2 : IsSimpleGroup (PrimePowerModel 2 1) :=
  primePower_simple 2 1

theorem noncommutative_q2 : ¬ IsMulCommutative (PrimePowerModel 2 1) :=
  primePower_noncommutative 2 1

theorem order_q3 : Nat.card (PrimePowerModel 3 1) = 20560831566912 := by
  have h := primePower_order 3 1 (by omega)
  norm_num at h ⊢
  exact h

theorem simple_q3 : IsSimpleGroup (PrimePowerModel 3 1) :=
  primePower_simple 3 1

theorem noncommutative_q3 : ¬ IsMulCommutative (PrimePowerModel 3 1) :=
  primePower_noncommutative 3 1

theorem order_q4 : Nat.card (PrimePowerModel 2 2) = 67802350642790400 := by
  have h := primePower_order 2 2 (by omega)
  norm_num at h ⊢
  exact h

theorem simple_q4 : IsSimpleGroup (PrimePowerModel 2 2) :=
  primePower_simple 2 2

theorem noncommutative_q4 : ¬ IsMulCommutative (PrimePowerModel 2 2) :=
  primePower_noncommutative 2 2


theorem extension_card_q2 :
    Nat.card (FiniteField.Extension (GaloisField 2 1) 2 3) = 8 := by
  rw [FiniteCubic.card_extension (FiniteField.finrank_extension (GaloisField 2 1) 2 3),
    GaloisField.card 2 1 (by decide)]
  norm_num

theorem unipotent_card_q2 :
    Nat.card (unipotent (GaloisField 2 1)
      (FiniteField.Extension (GaloisField 2 1) 2 3)
      (FiniteField.finrank_extension (GaloisField 2 1) 2 3)) = 4096 := by
  rw [card_unipotent, GaloisField.card 2 1 (by decide)]
  norm_num

theorem extension_card_q3 :
    Nat.card (FiniteField.Extension (GaloisField 3 1) 3 3) = 27 := by
  rw [FiniteCubic.card_extension (FiniteField.finrank_extension (GaloisField 3 1) 3 3),
    GaloisField.card 3 1 (by decide)]
  norm_num

theorem unipotent_card_q3 :
    Nat.card (unipotent (GaloisField 3 1)
      (FiniteField.Extension (GaloisField 3 1) 3 3)
      (FiniteField.finrank_extension (GaloisField 3 1) 3 3)) = 531441 := by
  rw [card_unipotent, GaloisField.card 3 1 (by decide)]
  norm_num

theorem extension_card_q4 :
    Nat.card (FiniteField.Extension (GaloisField 2 2) 2 3) = 64 := by
  rw [FiniteCubic.card_extension (FiniteField.finrank_extension (GaloisField 2 2) 2 3),
    GaloisField.card 2 2 (by decide)]
  norm_num

theorem unipotent_card_q4 :
    Nat.card (unipotent (GaloisField 2 2)
      (FiniteField.Extension (GaloisField 2 2) 2 3)
      (FiniteField.finrank_extension (GaloisField 2 2) 2 3)) = 16777216 := by
  rw [card_unipotent, GaloisField.card 2 2 (by decide)]
  norm_num

end Atlas.Triality

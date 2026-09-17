import Atlas.Fischer.ParkerStandardOrder
import Atlas.Mathieu.Mathieu24PointOrders

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual Parker subgroup whose coordinate permutation fixes the marked tuple. -/
def parkerMarkedStabilizer {k : ℕ} (e : Fin k ↪ Omega) : Subgroup ParkerStandardGroup :=
  (orderedPointStabilizer e).comap parkerStandardProjection

theorem parkerMarkedStabilizer_order {k : ℕ} (e : Fin k ↪ Omega) :
    Nat.card (parkerMarkedStabilizer e) = 4096 * Nat.card (orderedPointStabilizer e) := by
  have hc := (parkerMarkedStabilizer e).card_mul_index
  have hi : (parkerMarkedStabilizer e).index = (orderedPointStabilizer e).index :=
    Subgroup.index_comap_of_surjective _ parkerStandardProjection_surjective
  rw [hi, parkerStandardGroup_order] at hc
  have hd := (orderedPointStabilizer e).card_mul_index
  have hp : 0 < (orderedPointStabilizer e).index := by
    rw [mathieu24_order] at hd
    by_contra h
    have hz : (orderedPointStabilizer e).index = 0 := by omega
    rw [hz] at hd
    norm_num at hd
  nlinarith

theorem parkerMarkedStabilizer_five_order (e : Fin 5 ↪ Omega) :
    Nat.card (parkerMarkedStabilizer e) = 196608 := by
  rw [parkerMarkedStabilizer_order, mathieu24_five_point_order]

end Atlas.Fischer

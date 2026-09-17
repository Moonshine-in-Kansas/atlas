import Atlas.Conway.GolayTwoCoordinateFiber
import Mathlib.GroupTheory.Coset.Basic

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

def golayCoordinateSum (i j : Omega) : golay →ₗ[Bit] Bit where
  toFun c := c.val i + c.val j
  map_add' c d := by change c.val i + d.val i + (c.val j + d.val j) = _; abel
  map_smul' r c := by change r * c.val i + r * c.val j = r * (c.val i + c.val j); ring

theorem golayCoordinateSum_surjective (i j : Omega) (hij : i ≠ j) :
    Function.Surjective (golayCoordinateSum i j) := by
  intro b
  obtain ⟨c,hc⟩ := golay_two_coordinates_surjective i j hij (0,b)
  have hi := congrArg Prod.fst hc
  have hj := congrArg Prod.snd hc
  change c.val i = 0 at hi
  change c.val j = b at hj
  exact ⟨c,by change c.val i + c.val j = b; rw [hi,hj,zero_add]⟩

theorem golayCoordinateSum_kernel_finrank (i j : Omega) (hij : i ≠ j) :
    Module.finrank Bit (golayCoordinateSum i j).ker = 11 := by
  have he := (golayCoordinateSum i j).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (golayCoordinateSum_surjective i j hij),finrank_top,
    golay_finrank,Module.finrank_self] at he
  omega

theorem golayCoordinateSum_kernel_card (i j : Omega) (hij : i ≠ j) :
    Nat.card (golayCoordinateSum i j).ker = 2048 := by
  rw [Module.natCard_eq_pow_finrank (K := Bit),golayCoordinateSum_kernel_finrank i j hij]
  simp [Bit]

def GolayOppositeCoordinates (i j : Omega) := {c : golay // c.val i ≠ c.val j}

theorem golayOppositeCoordinates_card (i j : Omega) (hij : i ≠ j) :
    Nat.card (GolayOppositeCoordinates i j) = 2048 := by
  have he := Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective
    (f := (golayCoordinateSum i j).toAddMonoidHom) (golayCoordinateSum_surjective i j hij) 1)
  change Nat.card {c : golay // golayCoordinateSum i j c = 1} = Nat.card (golayCoordinateSum i j).ker at he
  have e : GolayOppositeCoordinates i j ≃ {c : golay // golayCoordinateSum i j c = 1} :=
    Equiv.subtypeEquivRight (fun c => by
      change c.val i ≠ c.val j ↔ c.val i + c.val j = 1
      rcases bit_cases (c.val i) with hi | hi <;>
        rcases bit_cases (c.val j) with hj | hj <;> simp [hi,hj])
  rw [Nat.card_congr e,he,golayCoordinateSum_kernel_card i j hij]

end Atlas.Conway

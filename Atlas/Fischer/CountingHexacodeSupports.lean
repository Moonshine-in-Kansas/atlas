import Atlas.Fischer.CountingHexacodeWeights
import Atlas.Codes.HexacodeZeroFibers

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def countingHexCoordinate (i : Fin 6) : countingHexacode →ₗ[CountingFour] CountingFour :=
  (LinearMap.proj i).comp countingHexacode.subtype

def countingHexDoubleZero (i j : Fin 6) : Submodule CountingFour countingHexacode :=
  (countingHexCoordinate i).ker ⊓ (countingHexCoordinate j).ker

def countingHexDoubleZeroEquiv (i j : Fin 6) :
    hexDoubleZero (hexPos i) (hexPos j) ≃ countingHexDoubleZero i j :=
  Equiv.subtypeEquiv countingHexEquiv (by
    intro h
    change (h.val (hexPos i)=0 ∧ h.val (hexPos j)=0) ↔
      (countingHexCoordinates h.val i=0 ∧ countingHexCoordinates h.val j=0)
    have hz (k : Fin 6) : countingHexCoordinates h.val k=0 ↔ h.val (hexPos k)=0 := by
      change countingLetterEquiv (countingHexLocal k (h.val (hexPos k)))=0 ↔ _
      rw [LinearEquiv.map_eq_zero_iff,LinearEquiv.map_eq_zero_iff]
    rw [hz,hz])

theorem countingHexDoubleZero_card (i j : Fin 6) (hij : i ≠ j) :
    Nat.card (countingHexDoubleZero i j)=4 := by
  rw [← Nat.card_congr (countingHexDoubleZeroEquiv i j)]
  exact hexDoubleZero_card _ _ (fun he => hij (hexIndexEquiv.symm.injective he))

/-- Exactly three nonzero source words vanish in a prescribed pair of columns. -/
theorem countingHexDoubleZero_nonzero_card (i j : Fin 6) (hij : i ≠ j) :
    Nat.card {h : countingHexDoubleZero i j // h ≠ 0}=3 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [Finset.filter_ne',Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ]
  rw [← Nat.card_eq_fintype_card,countingHexDoubleZero_card i j hij]

theorem countingHexacode_weights (h : countingHexacode) :
    hammingNorm h.val=0 ∨ hammingNorm h.val=4 ∨ hammingNorm h.val=6 := by
  obtain ⟨w,rfl⟩ := countingHexEquiv.surjective h
  change hammingNorm (countingHexCoordinates w.val)=0 ∨
    hammingNorm (countingHexCoordinates w.val)=4 ∨ hammingNorm (countingHexCoordinates w.val)=6
  rw [countingHexCoordinates_weight]
  exact hex_weights w

/-- These three words have exactly the complementary four-set as their support. -/
theorem countingHexDoubleZero_nonzero_support (i j : Fin 6) (hij : i ≠ j)
    (h : countingHexDoubleZero i j) (hh : h ≠ 0) (k : Fin 6) :
    h.val.val k=0 ↔ k=i ∨ k=j := by
  let Z := Finset.univ.filter (fun k : Fin 6 => h.val.val k=0)
  have hsum : Z.card+hammingNorm h.val.val=6 := by
    exact Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun k : Fin 6 => h.val.val k=0)
  have hi : i ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.property.1⟩
  have hj : j ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.property.2⟩
  have hZ : 0 < Z.card := Finset.card_pos.mpr ⟨i,hi⟩
  have hn : hammingNorm h.val.val ≠ 0 := by
    intro he
    exact hh (Subtype.ext (Subtype.ext (hammingNorm_eq_zero.mp he)))
  have hw := countingHexacode_weights h.val
  have hc : Z.card=2 := by omega
  have hs : ({i,j} : Finset (Fin 6)) ⊆ Z := by simp [Finset.insert_subset_iff,hi,hj]
  have he : ({i,j} : Finset (Fin 6))=Z := Finset.eq_of_subset_of_card_le hs (by simp [hc,hij])
  have hz : k ∈ Z ↔ k=i ∨ k=j := by rw [← he]; simp
  simpa [Z] using hz

end Atlas.Fischer

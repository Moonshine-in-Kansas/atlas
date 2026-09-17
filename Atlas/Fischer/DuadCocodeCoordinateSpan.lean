import Atlas.Fischer.CoordinateCocodeSpans
import Atlas.Fischer.DuadCocode

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem coordinateCocodeSpan_le_duadAnnihilator (p : Finset Omega) :
    coordinateCocodeSpan p ≤ duadCocodeAnnihilator p := by
  apply Submodule.span_le.mpr
  rintro d ⟨i,hi,rfl⟩
  change coordinateCocode i ∈ duadCocodeAnnihilator p
  rw [mem_duadCocodeAnnihilator]
  intro c
  rw [cocodePairing_coordinate]
  exact (mem_duadShortenedCode p c.val).mp c.prop i hi

/-- The actual shortened-duad annihilator is exactly the span of its two
marked coordinate cocode generators, with both inclusions justified. -/
theorem duadCocodeAnnihilator_eq_coordinateSpan (p : Finset Omega) (hp : p.card=2) :
    duadCocodeAnnihilator p=coordinateCocodeSpan p := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq (coordinateCocodeSpan_le_duadAnnihilator p)
  rw [coordinateCocodeSpan_finrank p (by omega),duadCocodeAnnihilator_finrank p hp,hp]

/-- Two distinct duads through a coordinate have precisely that singleton
coordinate cocode line in common. -/
theorem duadCocodeAnnihilator_pair_inter_pair (i j k : Omega)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    duadCocodeAnnihilator {i,j} ⊓ duadCocodeAnnihilator {i,k}=coordinateCocodeSpan {i} := by
  classical
  rw [duadCocodeAnnihilator_eq_coordinateSpan _ (by simp [hij]),
    duadCocodeAnnihilator_eq_coordinateSpan _ (by simp [hik]),
    coordinateCocodeSpan_pair_inter_pair i j k hij hik hjk]

end Atlas.Fischer

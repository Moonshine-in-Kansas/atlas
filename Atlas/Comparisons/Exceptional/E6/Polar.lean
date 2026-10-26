import Atlas.Comparisons.Exceptional.E6.Lattice

/-! The displayed Gram matrix is the polar form of the displayed quadratic form. -/
namespace Atlas.Comparisons.E6Lattice
open Matrix

theorem polar_gram {R : Type*} [CommRing R] (x y : Fin 6 → R) :
    norm (x+y) - norm x - norm y =
      ∑ i : Fin 6, x i * ((gram.map (Int.castRingHom R)) *ᵥ y) i := by
  simp [norm,gram,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

end Atlas.Comparisons.E6Lattice

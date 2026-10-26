import Atlas.Algebra.Albert.Adjoint

namespace Atlas.Albert
variable {F : Type*} [CommRing F]

theorem tracePairing_add_left (x y z : Carrier F) :
    tracePairing (x + y) z = tracePairing x z + tracePairing y z := by
  simp [tracePairing, trace, quadraticTrace, SplitOctonion.norm]; ring

theorem tracePairing_smul_left (t : F) (x y : Carrier F) :
    tracePairing (t • x) y = t * tracePairing x y := by
  simp [tracePairing, trace, quadraticTrace, SplitOctonion.norm]; ring

def basisVector (i : Coordinate) : Carrier F :=
  (fun j => (Pi.single i (1 : F) : Coordinate → F) (.inl j), fun j k => (Pi.single i (1 : F) : Coordinate → F) (.inr (j,k)))

theorem tracePairing_diagonal_basis (x : Carrier F) (i : Fin 3) :
    tracePairing x (basisVector (.inl i)) = x.1 i := by
  fin_cases i <;>
    simp [tracePairing, trace, quadraticTrace, SplitOctonion.norm, basisVector,
      Pi.single_apply] <;> ring

set_option maxHeartbeats 800000 in
theorem tracePairing_octonion_basis (x : Carrier F) (i : Fin 3) (j : Fin 8) :
    tracePairing x (basisVector (.inr (i,j))) = x.2 i (7-j) := by
  fin_cases i <;> fin_cases j <;>
    simp [tracePairing, trace, quadraticTrace, SplitOctonion.norm, basisVector,
      Pi.single_apply] <;> ring

/-- No division by two or three: the pairing is already nondegenerate over rings. -/
theorem tracePairing_nondegenerate (x : Carrier F)
    (h : ∀ y, tracePairing x y = 0) : x = 0 := by
  apply Prod.ext
  · funext i
    exact (tracePairing_diagonal_basis x i).symm.trans (h _)
  · funext i j
    have hh := (tracePairing_octonion_basis x i (7-j)).symm.trans (h _)
    simpa using hh

end Atlas.Albert

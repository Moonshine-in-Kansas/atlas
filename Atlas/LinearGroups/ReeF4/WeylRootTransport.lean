import Atlas.LinearGroups.ReeF4.WeylCoordinateTransport

namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F]

def weylRootMark (r : ShortRootLabel) : WeylCoordinate :=
  (r.1, (![(0 : Fin 9),1,2,3,5,6,7,8]) r.2)

set_option maxHeartbeats 400000 in
theorem weylCoordinateRead_root (r : ShortRootLabel) (c : WeylCoordinate) :
    weylCoordinateRead (rootVector (F := F) r) c =
      if c = weylRootMark r then 1 else 0 := by
  rcases r with ⟨b,j⟩
  rcases c with ⟨i,k⟩
  by_cases hi : i = b
  · subst i
    fin_cases j <;> fin_cases k <;>
      simp [weylCoordinateRead, rootVector, wilsonCoordinatesEquiv, weylRootMark,
        Pi.single_apply]
  · fin_cases k <;>
      simp [weylCoordinateRead, rootVector, wilsonCoordinatesEquiv, weylRootMark,
        Pi.single_apply, hi]

theorem weylCoordinateCompatible_root
    {e : TraceZero F ≃ₗ[F] TraceZero F} {p : Equiv.Perm WeylCoordinate}
    (he : WeylCoordinateCompatible e p) (r s : ShortRootLabel)
    (hp : p (weylRootMark r) = weylRootMark s) :
    e (rootVector r) = rootVector s := by
  apply Subtype.ext
  apply (wilsonCoordinatesEquiv (F := F)).injective
  funext i j
  change weylCoordinateRead (e (rootVector r)) (i,j) =
    weylCoordinateRead (rootVector s) (i,j)
  rw [he (rootVector r) (i,j)]
  simp only [weylCoordinateRead_root, Equiv.symm_apply_eq, hp]

end Atlas.ReeF4

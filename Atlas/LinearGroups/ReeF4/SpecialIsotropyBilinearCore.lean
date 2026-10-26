import Atlas.LinearGroups.ReeF4.SpecialIsotropyData

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F R : Type*} [CommRing F] [CommRing R] [CharP F 2] [CharP R 2]

theorem isotropyCoordinates_map (f : F →+* R) (u : TraceZero F) :
    isotropyCoordinates (traceZeroMap f u) = fun k => f (isotropyCoordinates u k) := by
  funext k
  fin_cases k <;> rfl

theorem isotropyMarkedBasis_map (f : F →+* R) (i : TraceZeroCoordinate) :
    traceZeroMap f (markedBasis (F := F) i) = markedBasis (F := R) i := by
  cases i with
  | inl i => simp only [markedBasis_diagonal,diagonalVector_map]
  | inr i => simp only [markedBasis_root,rootVector_map]

theorem isotropyRawStar_map (f : F →+* R) (x y : Fin 26 → F) :
    isotropyRawStar (fun k => f (x k)) (fun k => f (y k)) =
      fun k => f (isotropyRawStar x y k) := by
  funext k
  fin_cases k <;> simp [isotropyRawStar,_root_.map_add,_root_.map_mul]

private def isotropyMonomial (i j : Fin 26) :
    (Fin 26 → F) →ₗ[F] (Fin 26 → F) →ₗ[F] F where
  toFun x :=
    { toFun := fun y => x i * y j
      map_add' := by intro y z; exact mul_add _ _ _
      map_smul' := by intro a y; change x i * (a*y j) = a*(x i*y j); ring }
  map_add' := by
    intro x z
    apply LinearMap.ext
    intro y
    exact add_mul _ _ _
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    change (a*x i)*y j=a*(x i*y j)
    exact mul_assoc _ _ _

private def isotropyRowBilinear : Fin 26 →
    ((Fin 26 → F) →ₗ[F] (Fin 26 → F) →ₗ[F] F) :=
  ![(isotropyMonomial 3 8 + isotropyMonomial 8 3) + (isotropyMonomial 4 7 + isotropyMonomial 7 4) + (isotropyMonomial 11 16 + isotropyMonomial 16 11) + (isotropyMonomial 12 15 + isotropyMonomial 15 12) + (isotropyMonomial 19 24 + isotropyMonomial 24 19) + (isotropyMonomial 20 23 + isotropyMonomial 23 20),(isotropyMonomial 0 1 + isotropyMonomial 1 0) + (isotropyMonomial 4 7 + isotropyMonomial 7 4) + (isotropyMonomial 5 6 + isotropyMonomial 6 5) + (isotropyMonomial 12 15 + isotropyMonomial 15 12) + (isotropyMonomial 13 14 + isotropyMonomial 14 13) + (isotropyMonomial 20 23 + isotropyMonomial 23 20) + (isotropyMonomial 21 22 + isotropyMonomial 22 21),(isotropyMonomial 2 3 + isotropyMonomial 3 2) + (isotropyMonomial 10 11 + isotropyMonomial 11 10) + (isotropyMonomial 18 19 + isotropyMonomial 19 18),(isotropyMonomial 2 8 + isotropyMonomial 8 2) + (isotropyMonomial 12 13 + isotropyMonomial 13 12) + (isotropyMonomial 20 22 + isotropyMonomial 22 20),(isotropyMonomial 4 5 + isotropyMonomial 5 4) + (isotropyMonomial 12 14 + isotropyMonomial 14 12) + (isotropyMonomial 18 24 + isotropyMonomial 24 18),(isotropyMonomial 4 6 + isotropyMonomial 6 4) + (isotropyMonomial 10 16 + isotropyMonomial 16 10) + (isotropyMonomial 20 21 + isotropyMonomial 21 20),(isotropyMonomial 5 7 + isotropyMonomial 7 5) + (isotropyMonomial 11 17 + isotropyMonomial 17 11) + (isotropyMonomial 22 23 + isotropyMonomial 23 22),(isotropyMonomial 6 7 + isotropyMonomial 7 6) + (isotropyMonomial 13 15 + isotropyMonomial 15 13) + (isotropyMonomial 19 25 + isotropyMonomial 25 19),(isotropyMonomial 3 9 + isotropyMonomial 9 3) + (isotropyMonomial 14 15 + isotropyMonomial 15 14) + (isotropyMonomial 21 23 + isotropyMonomial 23 21),(isotropyMonomial 8 9 + isotropyMonomial 9 8) + (isotropyMonomial 16 17 + isotropyMonomial 17 16) + (isotropyMonomial 24 25 + isotropyMonomial 25 24),(isotropyMonomial 2 5 + isotropyMonomial 5 2) + (isotropyMonomial 11 12 + isotropyMonomial 12 11) + (isotropyMonomial 18 22 + isotropyMonomial 22 18),(isotropyMonomial 2 6 + isotropyMonomial 6 2) + (isotropyMonomial 10 13 + isotropyMonomial 13 10) + (isotropyMonomial 19 20 + isotropyMonomial 20 19),(isotropyMonomial 3 4 + isotropyMonomial 4 3) + (isotropyMonomial 10 14 + isotropyMonomial 14 10) + (isotropyMonomial 18 21 + isotropyMonomial 21 18),(isotropyMonomial 3 7 + isotropyMonomial 7 3) + (isotropyMonomial 11 15 + isotropyMonomial 15 11) + (isotropyMonomial 19 23 + isotropyMonomial 23 19),(isotropyMonomial 4 8 + isotropyMonomial 8 4) + (isotropyMonomial 12 16 + isotropyMonomial 16 12) + (isotropyMonomial 20 24 + isotropyMonomial 24 20),(isotropyMonomial 7 8 + isotropyMonomial 8 7) + (isotropyMonomial 13 17 + isotropyMonomial 17 13) + (isotropyMonomial 22 25 + isotropyMonomial 25 22),(isotropyMonomial 5 9 + isotropyMonomial 9 5) + (isotropyMonomial 14 17 + isotropyMonomial 17 14) + (isotropyMonomial 23 24 + isotropyMonomial 24 23),(isotropyMonomial 6 9 + isotropyMonomial 9 6) + (isotropyMonomial 15 16 + isotropyMonomial 16 15) + (isotropyMonomial 21 25 + isotropyMonomial 25 21),(isotropyMonomial 2 4 + isotropyMonomial 4 2) + (isotropyMonomial 10 12 + isotropyMonomial 12 10) + (isotropyMonomial 18 20 + isotropyMonomial 20 18),(isotropyMonomial 2 7 + isotropyMonomial 7 2) + (isotropyMonomial 11 13 + isotropyMonomial 13 11) + (isotropyMonomial 19 22 + isotropyMonomial 22 19),(isotropyMonomial 3 5 + isotropyMonomial 5 3) + (isotropyMonomial 11 14 + isotropyMonomial 14 11) + (isotropyMonomial 18 23 + isotropyMonomial 23 18),(isotropyMonomial 5 8 + isotropyMonomial 8 5) + (isotropyMonomial 12 17 + isotropyMonomial 17 12) + (isotropyMonomial 22 24 + isotropyMonomial 24 22),(isotropyMonomial 3 6 + isotropyMonomial 6 3) + (isotropyMonomial 10 15 + isotropyMonomial 15 10) + (isotropyMonomial 19 21 + isotropyMonomial 21 19),(isotropyMonomial 6 8 + isotropyMonomial 8 6) + (isotropyMonomial 13 16 + isotropyMonomial 16 13) + (isotropyMonomial 20 25 + isotropyMonomial 25 20),(isotropyMonomial 4 9 + isotropyMonomial 9 4) + (isotropyMonomial 14 16 + isotropyMonomial 16 14) + (isotropyMonomial 21 24 + isotropyMonomial 24 21),(isotropyMonomial 7 9 + isotropyMonomial 9 7) + (isotropyMonomial 15 17 + isotropyMonomial 17 15) + (isotropyMonomial 23 25 + isotropyMonomial 25 23)]

private def isotropyBuiltBilinear :
    (Fin 26 → F) →ₗ[F] (Fin 26 → F) →ₗ[F] (Fin 26 → F) where
  toFun x := LinearMap.pi (fun k => isotropyRowBilinear k x)
  map_add' := by
    intro x z
    apply LinearMap.ext
    intro y
    funext k
    exact congrArg (fun f : (Fin 26 → F) →ₗ[F] F => f y)
      ((isotropyRowBilinear k).map_add x z)
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    funext k
    exact congrArg (fun f : (Fin 26 → F) →ₗ[F] F => f y)
      ((isotropyRowBilinear k).map_smul a x)

private theorem isotropyBuiltBilinear_apply (x y : Fin 26 → F) :
    isotropyBuiltBilinear x y = isotropyRawStar x y := by
  funext k
  fin_cases k <;> rfl

/-- Retains the original definitional evaluation; linearity comes from a
sum of elementary bilinear maps, not repeated polynomial expansion. -/
def isotropyRawBilinear : (Fin 26 → F) →ₗ[F] (Fin 26 → F) →ₗ[F] (Fin 26 → F) where
  toFun x :=
    { toFun := isotropyRawStar x
      map_add' := by
        intro y z
        simp only [←isotropyBuiltBilinear_apply,_root_.map_add]
      map_smul' := by
        intro a y
        simp only [←isotropyBuiltBilinear_apply,LinearMap.map_smul,RingHom.id_apply] }
  map_add' := by
    intro x z
    apply LinearMap.ext
    intro y
    change isotropyRawStar (x+z) y = isotropyRawStar x y + isotropyRawStar z y
    simp only [←isotropyBuiltBilinear_apply,_root_.map_add,LinearMap.add_apply]
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    change isotropyRawStar (a • x) y = a • isotropyRawStar x y
    simp only [←isotropyBuiltBilinear_apply,LinearMap.map_smul,LinearMap.smul_apply,RingHom.id_apply]

def isotropyRawOnTraceZero : TraceZero F →ₗ[F] TraceZero F →ₗ[F] (Fin 26 → F) :=
  { toFun := fun u => (isotropyRawBilinear (isotropyCoordinates u)).comp isotropyCoordinates
    map_add' := by
      intro u v
      apply LinearMap.ext
      intro w
      change isotropyRawBilinear (isotropyCoordinates (u+v)) (isotropyCoordinates w) =
        isotropyRawBilinear (isotropyCoordinates u) (isotropyCoordinates w) +
        isotropyRawBilinear (isotropyCoordinates v) (isotropyCoordinates w)
      rw [_root_.map_add,_root_.map_add]
      rfl
    map_smul' := by
      intro a u
      apply LinearMap.ext
      intro w
      change isotropyRawBilinear (isotropyCoordinates (a • u)) (isotropyCoordinates w) =
        a • isotropyRawBilinear (isotropyCoordinates u) (isotropyCoordinates w)
      rw [LinearMap.map_smul,LinearMap.map_smul]
      rfl }

def isotropyActualBilinear : TraceZero F →ₗ[F] TraceZero F →ₗ[F] (Fin 26 → F) where
  toFun u :=
    { toFun := fun v => isotropyCoordinates (proposedStarLinear (wedge u v))
      map_add' := by intro v w; simp only [wedge_add_right,_root_.map_add]
      map_smul' := by intro a v; simp only [wedge_smul_right,LinearMap.map_smul,RingHom.id_apply] }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    change isotropyCoordinates (proposedStarLinear (wedge (u + v) w)) = _
    simp only [wedge_add_left,_root_.map_add,LinearMap.add_apply]
    rfl
  map_smul' := by
    intro a u
    apply LinearMap.ext
    intro w
    change isotropyCoordinates (proposedStarLinear (wedge (a • u) w)) = _
    simp only [wedge_smul_left,LinearMap.map_smul,LinearMap.smul_apply,RingHom.id_apply]
    rfl

end Atlas.ReeF4

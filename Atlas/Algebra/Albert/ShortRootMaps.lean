import Atlas.Algebra.Albert.Cubic

/-! Wilson's short-root transformations in the first two diagonal positions.
The parameter octonion is a multiple of any one of the eight marked isotropic
basis vectors, including the two idempotents of nonzero trace. All identities
below are integral polynomial identities, not finite-field value tests. -/
namespace Atlas.Albert
variable {F : Type*} [CommRing F]

def shortRootFormula (x : SplitOctonion.Carrier F) (y : Carrier F) : Carrier F :=
  let pairing := SplitOctonion.trace (SplitOctonion.mul (y.2 2) (SplitOctonion.conjugate x))
  (![y.1 0 - pairing, y.1 1 + pairing, y.1 2],
   ![y.2 0 + SplitOctonion.conjugate (SplitOctonion.mul (y.2 1) x),
     y.2 1 - SplitOctonion.conjugate (SplitOctonion.mul x (y.2 0)),
     y.2 2 + (y.1 0 - y.1 1) • x -
       SplitOctonion.mul x (SplitOctonion.mul (SplitOctonion.conjugate (y.2 2)) x)])

set_option maxHeartbeats 1800000 in
theorem shortRootFormula_add (x : SplitOctonion.Carrier F) (y z : Carrier F) :
    shortRootFormula x (y + z) = shortRootFormula x y + shortRootFormula x z := by
  apply Prod.ext
  · funext i; fin_cases i <;>
      simp [Matrix.vecHead, Matrix.vecTail, shortRootFormula, SplitOctonion.trace, SplitOctonion.mul,
        SplitOctonion.conjugate, SplitOctonion.unit] <;> ring
  · funext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecHead, Matrix.vecTail, shortRootFormula, SplitOctonion.trace, SplitOctonion.mul,
        SplitOctonion.conjugate, SplitOctonion.unit] <;> ring

set_option maxHeartbeats 1800000 in
theorem shortRootFormula_smul (x : SplitOctonion.Carrier F) (t : F) (y : Carrier F) :
    shortRootFormula x (t • y) = t • shortRootFormula x y := by
  apply Prod.ext
  · funext i; fin_cases i <;>
      simp [Matrix.vecHead, Matrix.vecTail, shortRootFormula, SplitOctonion.trace, SplitOctonion.mul,
        SplitOctonion.conjugate, SplitOctonion.unit] <;> ring
  · funext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecHead, Matrix.vecTail, shortRootFormula, SplitOctonion.trace, SplitOctonion.mul,
        SplitOctonion.conjugate, SplitOctonion.unit] <;> ring

def shortRootLinear (i : Fin 8) (t : F) : Carrier F →ₗ[F] Carrier F where
  toFun := shortRootFormula (t • SplitOctonion.basisVector i)
  map_add' := shortRootFormula_add _
  map_smul' := shortRootFormula_smul _

theorem shortRootLinear_apply (i : Fin 8) (t : F) (y : Carrier F) :
    shortRootLinear i t y = shortRootFormula (t • SplitOctonion.basisVector i) y := rfl

theorem shortRootFormula_unit (x : SplitOctonion.Carrier F) :
    shortRootFormula x (unit : Carrier F) = unit := by
  apply Prod.ext
  · funext i; fin_cases i <;>
      simp [Matrix.vecHead, Matrix.vecTail, shortRootFormula, unit, SplitOctonion.trace, SplitOctonion.mul,
        SplitOctonion.conjugate, SplitOctonion.unit]
  · funext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecHead, Matrix.vecTail, shortRootFormula, unit, SplitOctonion.trace, SplitOctonion.mul,
        SplitOctonion.conjugate, SplitOctonion.unit]

theorem shortRootLinear_zero (i : Fin 8) (y : Carrier F) : shortRootLinear i 0 y = y := by
  apply Prod.ext
  · funext j; fin_cases j <;>
      simp [Matrix.vecHead, Matrix.vecTail, shortRootLinear, shortRootFormula, SplitOctonion.trace, SplitOctonion.mul,
        SplitOctonion.conjugate, SplitOctonion.unit]
  · funext j k; fin_cases j <;> fin_cases k <;>
      simp [Matrix.vecHead, Matrix.vecTail, shortRootLinear, shortRootFormula, SplitOctonion.trace, SplitOctonion.mul,
        SplitOctonion.conjugate, SplitOctonion.unit]

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 4096 in
theorem shortRootLinear_add (i : Fin 8) (s t : F) (y : Carrier F) :
    shortRootLinear i s (shortRootLinear i t y) = shortRootLinear i (s + t) y := by
  fin_cases i <;> apply Prod.ext
  all_goals solve
    | (funext j k; fin_cases j <;> fin_cases k <;>
        simp [Matrix.vecHead, Matrix.vecTail, shortRootLinear, shortRootFormula, SplitOctonion.basisVector,
          Pi.single_apply, SplitOctonion.trace, SplitOctonion.mul,
          SplitOctonion.conjugate, SplitOctonion.unit] <;> ring)
    | (funext j; fin_cases j <;>
        simp [Matrix.vecHead, Matrix.vecTail, shortRootLinear, shortRootFormula, SplitOctonion.basisVector,
          Pi.single_apply, SplitOctonion.trace, SplitOctonion.mul,
          SplitOctonion.conjugate, SplitOctonion.unit] <;> ring)

def shortRootEquiv (i : Fin 8) (t : F) : Carrier F ≃ₗ[F] Carrier F where
  toLinearMap := shortRootLinear i t
  invFun := shortRootLinear i (-t)
  left_inv y := by
    change shortRootLinear i (-t) (shortRootLinear i t y) = y
    rw [shortRootLinear_add, neg_add_cancel, shortRootLinear_zero]
  right_inv y := by
    change shortRootLinear i t (shortRootLinear i (-t) y) = y
    rw [shortRootLinear_add, add_neg_cancel, shortRootLinear_zero]

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 4096 in
theorem shortRootLinear_norm (i : Fin 8) (t : F) (y : Carrier F) :
    norm (shortRootLinear i t y) = norm y := by
  fin_cases i <;>
    simp [Matrix.vecHead, Matrix.vecTail, shortRootLinear, shortRootFormula, SplitOctonion.basisVector,
      Pi.single_apply, norm, SplitOctonion.norm, SplitOctonion.trace,
      SplitOctonion.mul, SplitOctonion.conjugate, SplitOctonion.unit] <;> ring

theorem shortRootEquiv_unit (i : Fin 8) (t : F) :
    shortRootEquiv i t (unit : Carrier F) = unit := shortRootFormula_unit _

theorem shortRootEquiv_norm (i : Fin 8) (t : F) (y : Carrier F) :
    norm (shortRootEquiv i t y) = norm y := shortRootLinear_norm i t y

end Atlas.Albert

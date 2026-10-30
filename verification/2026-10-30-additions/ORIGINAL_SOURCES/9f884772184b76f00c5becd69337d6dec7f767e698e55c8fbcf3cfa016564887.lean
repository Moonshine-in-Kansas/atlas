import Atlas.LinearGroups.F4.TorusLongRootMaps
import Atlas.LinearGroups.F4.ShortWeylRootPolynomial

/-! Source-only scalar checkpoint for the eight actual Albert simple-root
transformations, before comparison with the Geck model. Negative Geck
parameters are minus Wilson parameters. The literal formulas are retained
from repair10; this module imports no candidate integral matrix tables.
-/
namespace Atlas.Chevalley.Comparison.F4
open Atlas.Albert
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

variable {R : Type*} [CommRing R]

def albertSimpleApply (i : Fin 8) (t : R) (x : Carrier R) : Carrier R :=
  ![Atlas.F4.torusLongApply 0 t x,
    Atlas.F4.torusLongApply 2 t x,
    shortRootLinear 3 t x,
    coordinateCycle (coordinateCycle (shortRootLinear 3 t (coordinateCycle x))),
    Atlas.F4.torusLongApply 1 (-t) x,
    Atlas.F4.torusLongApply 3 (-t) x,
    shortRootLinear 4 (-t) x,
    coordinateCycle (coordinateCycle (shortRootLinear 4 (-t) (coordinateCycle x)))] i

/- The parameter formula uses the existing long- and short-root identities
over arbitrary commutative rings. Its two integer coefficient matrices are
identified in the separate `F4AlbertSimpleFormulas` continuation. -/
noncomputable def albertFirstCoefficient (i : Fin 8) (x : Carrier R) : Carrier R :=
  ![Atlas.F4.torusLongApply 0 1 x - x,
    Atlas.F4.torusLongApply 2 1 x - x,
    Atlas.F4.shortRootFirstCoefficient 3 x,
    coordinateCycle (coordinateCycle
      (Atlas.F4.shortRootFirstCoefficient 3 (coordinateCycle x))),
    -(Atlas.F4.torusLongApply 1 1 x - x),
    -(Atlas.F4.torusLongApply 3 1 x - x),
    -(Atlas.F4.shortRootFirstCoefficient 4 x),
    -(coordinateCycle (coordinateCycle
      (Atlas.F4.shortRootFirstCoefficient 4 (coordinateCycle x))))] i

noncomputable def albertSecondCoefficient (i : Fin 8) (x : Carrier R) : Carrier R :=
  ![0, 0,
    Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector 3) x,
    coordinateCycle (coordinateCycle
      (Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector 3)
        (coordinateCycle x))),
    0, 0,
    Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector 4) x,
    coordinateCycle (coordinateCycle
      (Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector 4)
        (coordinateCycle x)))] i

private theorem coordinateCycle_neg (x : Carrier R) :
    coordinateCycle (-x) = -coordinateCycle x :=
  _root_.map_neg (coordinateCycleEquiv (F := R)) x

theorem albertSimple_parameter (i : Fin 8) (t : R) (x : Carrier R) :
    albertSimpleApply i t x =
      x + t • albertFirstCoefficient i x + t^2 • albertSecondCoefficient i x := by
  fin_cases i
  · change Atlas.F4.torusLongApply 0 t x =
      x + t • (Atlas.F4.torusLongApply 0 1 x - x) + t^2 • (0 : Carrier R)
    simpa only [smul_zero, add_zero] using Atlas.F4.torusLongApply_parameter 0 t x
  · change Atlas.F4.torusLongApply 2 t x =
      x + t • (Atlas.F4.torusLongApply 2 1 x - x) + t^2 • (0 : Carrier R)
    simpa only [smul_zero, add_zero] using Atlas.F4.torusLongApply_parameter 2 t x
  · change shortRootLinear 3 t x = x + t • Atlas.F4.shortRootFirstCoefficient 3 x +
      t^2 • Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector 3) x
    exact Atlas.F4.shortRoot_polynomial 3 t x
  · change coordinateCycle (coordinateCycle (shortRootLinear 3 t (coordinateCycle x))) =
      x + t • coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootFirstCoefficient 3 (coordinateCycle x))) +
      t^2 • coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector 3)
          (coordinateCycle x)))
    rw [Atlas.F4.shortRoot_polynomial]
    simp only [coordinateCycle_add, coordinateCycle_smul, coordinateCycle_three]
  · change Atlas.F4.torusLongApply 1 (-t) x =
      x + t • (-(Atlas.F4.torusLongApply 1 1 x - x)) + t^2 • (0 : Carrier R)
    simpa only [neg_smul, smul_neg, smul_zero, add_zero] using
      Atlas.F4.torusLongApply_parameter 1 (-t) x
  · change Atlas.F4.torusLongApply 3 (-t) x =
      x + t • (-(Atlas.F4.torusLongApply 3 1 x - x)) + t^2 • (0 : Carrier R)
    simpa only [neg_smul, smul_neg, smul_zero, add_zero] using
      Atlas.F4.torusLongApply_parameter 3 (-t) x
  · change shortRootLinear 4 (-t) x = x + t • (-(Atlas.F4.shortRootFirstCoefficient 4 x)) +
      t^2 • Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector 4) x
    simpa only [neg_smul, smul_neg, neg_sq] using Atlas.F4.shortRoot_polynomial 4 (-t) x
  · change coordinateCycle (coordinateCycle (shortRootLinear 4 (-t) (coordinateCycle x))) =
      x + t • (-(coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootFirstCoefficient 4 (coordinateCycle x))))) +
      t^2 • coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector 4)
          (coordinateCycle x)))
    rw [Atlas.F4.shortRoot_polynomial]
    simp only [coordinateCycle_add, coordinateCycle_smul, coordinateCycle_three,
      neg_smul, smul_neg, neg_sq, coordinateCycle_neg]

private theorem albert_map_sub {S : Type*} [CommRing S] (f : R →+* S)
    (x y : Carrier R) : Atlas.Albert.map f (x - y) =
      Atlas.Albert.map f x - Atlas.Albert.map f y :=
  _root_.map_sub (Atlas.F4.albertMapAddHom f) x y

private theorem albert_map_neg {S : Type*} [CommRing S] (f : R →+* S)
    (x : Carrier R) : Atlas.Albert.map f (-x) = -Atlas.Albert.map f x :=
  _root_.map_neg (Atlas.F4.albertMapAddHom f) x

private theorem albert_map_zero {S : Type*} [CommRing S] (f : R →+* S) :
    Atlas.Albert.map f (0 : Carrier R) = 0 :=
  _root_.map_zero (Atlas.F4.albertMapAddHom f)

private theorem longFirst_map {S : Type*} [CommRing S] (f : R →+* S)
    (i : Fin 4) (x : Carrier R) :
    Atlas.F4.torusLongApply i 1 (Atlas.Albert.map f x) - Atlas.Albert.map f x =
      Atlas.Albert.map f (Atlas.F4.torusLongApply i 1 x - x) := by
  rw [← _root_.map_one f, Atlas.F4.torusLongApply_map, albert_map_sub]

private theorem cycledFirst_map {S : Type*} [CommRing S]
    (f : R →+* S) (j : Fin 8) (x : Carrier R) :
    coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootFirstCoefficient j (coordinateCycle (Atlas.Albert.map f x)))) =
      Atlas.Albert.map f (coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootFirstCoefficient j (coordinateCycle x)))) := by
  rw [coordinateCycle_map f x,
    Atlas.F4.shortRootFirstCoefficient_map f j (coordinateCycle x),
    coordinateCycle_map f (Atlas.F4.shortRootFirstCoefficient j (coordinateCycle x)),
    coordinateCycle_map f (coordinateCycle
      (Atlas.F4.shortRootFirstCoefficient j (coordinateCycle x)))]

private theorem cycledSecond_map {S : Type*} [CommRing S]
    (f : R →+* S) (j : Fin 8) (x : Carrier R) :
    coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector j)
          (coordinateCycle (Atlas.Albert.map f x)))) =
      Atlas.Albert.map f (coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector j)
          (coordinateCycle x)))) := by
  rw [coordinateCycle_map f x,
    Atlas.F4.shortRootQuadratic_basis_map f j (coordinateCycle x),
    coordinateCycle_map f (Atlas.F4.shortRootQuadraticLinear
      (Atlas.SplitOctonion.basisVector j) (coordinateCycle x)),
    coordinateCycle_map f (coordinateCycle (Atlas.F4.shortRootQuadraticLinear
      (Atlas.SplitOctonion.basisVector j) (coordinateCycle x)))]

/-- Naturality of the literal first coefficient, component by component. -/
theorem albertFirstCoefficient_map {S : Type*} [CommRing S]
    (f : R →+* S) (i : Fin 8) (x : Carrier R) :
    albertFirstCoefficient i (Atlas.Albert.map f x) =
      Atlas.Albert.map f (albertFirstCoefficient i x) := by
  fin_cases i
  · change Atlas.F4.torusLongApply 0 1 (Atlas.Albert.map f x) - Atlas.Albert.map f x =
      Atlas.Albert.map f (Atlas.F4.torusLongApply 0 1 x - x)
    exact longFirst_map f 0 x
  · change Atlas.F4.torusLongApply 2 1 (Atlas.Albert.map f x) - Atlas.Albert.map f x =
      Atlas.Albert.map f (Atlas.F4.torusLongApply 2 1 x - x)
    exact longFirst_map f 2 x
  · change Atlas.F4.shortRootFirstCoefficient 3 (Atlas.Albert.map f x) =
      Atlas.Albert.map f (Atlas.F4.shortRootFirstCoefficient 3 x)
    exact Atlas.F4.shortRootFirstCoefficient_map f 3 x
  · change coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootFirstCoefficient 3 (coordinateCycle (Atlas.Albert.map f x)))) =
      Atlas.Albert.map f (coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootFirstCoefficient 3 (coordinateCycle x))))
    exact cycledFirst_map f 3 x
  · change -(Atlas.F4.torusLongApply 1 1 (Atlas.Albert.map f x) - Atlas.Albert.map f x) =
      Atlas.Albert.map f (-(Atlas.F4.torusLongApply 1 1 x - x))
    rw [longFirst_map, albert_map_neg]
  · change -(Atlas.F4.torusLongApply 3 1 (Atlas.Albert.map f x) - Atlas.Albert.map f x) =
      Atlas.Albert.map f (-(Atlas.F4.torusLongApply 3 1 x - x))
    rw [longFirst_map, albert_map_neg]
  · change -(Atlas.F4.shortRootFirstCoefficient 4 (Atlas.Albert.map f x)) =
      Atlas.Albert.map f (-(Atlas.F4.shortRootFirstCoefficient 4 x))
    rw [Atlas.F4.shortRootFirstCoefficient_map, albert_map_neg]
  · change -(coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootFirstCoefficient 4 (coordinateCycle (Atlas.Albert.map f x))))) =
      Atlas.Albert.map f (-(coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootFirstCoefficient 4 (coordinateCycle x)))))
    rw [cycledFirst_map, albert_map_neg]

/-- Naturality of the literal second coefficient; negative parameters keep its sign. -/
theorem albertSecondCoefficient_map {S : Type*} [CommRing S]
    (f : R →+* S) (i : Fin 8) (x : Carrier R) :
    albertSecondCoefficient i (Atlas.Albert.map f x) =
      Atlas.Albert.map f (albertSecondCoefficient i x) := by
  fin_cases i
  · change (0 : Carrier S) = Atlas.Albert.map f (0 : Carrier R)
    exact (albert_map_zero f).symm
  · change (0 : Carrier S) = Atlas.Albert.map f (0 : Carrier R)
    exact (albert_map_zero f).symm
  · change Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector 3)
        (Atlas.Albert.map f x) =
      Atlas.Albert.map f (Atlas.F4.shortRootQuadraticLinear
        (Atlas.SplitOctonion.basisVector 3) x)
    exact Atlas.F4.shortRootQuadratic_basis_map f 3 x
  · change coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector 3)
          (coordinateCycle (Atlas.Albert.map f x)))) =
      Atlas.Albert.map f (coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector 3)
          (coordinateCycle x))))
    exact cycledSecond_map f 3 x
  · change (0 : Carrier S) = Atlas.Albert.map f (0 : Carrier R)
    exact (albert_map_zero f).symm
  · change (0 : Carrier S) = Atlas.Albert.map f (0 : Carrier R)
    exact (albert_map_zero f).symm
  · change Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector 4)
        (Atlas.Albert.map f x) =
      Atlas.Albert.map f (Atlas.F4.shortRootQuadraticLinear
        (Atlas.SplitOctonion.basisVector 4) x)
    exact Atlas.F4.shortRootQuadratic_basis_map f 4 x
  · change coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector 4)
          (coordinateCycle (Atlas.Albert.map f x)))) =
      Atlas.Albert.map f (coordinateCycle (coordinateCycle
        (Atlas.F4.shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector 4)
          (coordinateCycle x))))
    exact cycledSecond_map f 4 x


end Atlas.Chevalley.Comparison.F4

import Atlas.Algebra.Albert.ScalarMap
import Atlas.Algebra.SplitOctonion.TraceIdentities

namespace Atlas.Albert
variable {F : Type*} [CommRing F]

def coordinateCycle (x : Carrier F) : Carrier F :=
  (![x.1 1, x.1 2, x.1 0], ![x.2 1, x.2 2, x.2 0])

theorem coordinateCycle_add (x y : Carrier F) :
    coordinateCycle (x + y) = coordinateCycle x + coordinateCycle y := by
  apply Prod.ext
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem coordinateCycle_smul (t : F) (x : Carrier F) :
    coordinateCycle (t • x) = t • coordinateCycle x := by
  apply Prod.ext
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem coordinateCycle_three (x : Carrier F) :
    coordinateCycle (coordinateCycle (coordinateCycle x)) = x := by
  apply Prod.ext
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

def coordinateCycleEquiv : Carrier F ≃ₗ[F] Carrier F where
  toFun := coordinateCycle
  invFun x := coordinateCycle (coordinateCycle x)
  left_inv := coordinateCycle_three
  right_inv := coordinateCycle_three
  map_add' := coordinateCycle_add
  map_smul' := coordinateCycle_smul

theorem coordinateCycleEquiv_apply (x : Carrier F) :
    coordinateCycleEquiv x = coordinateCycle x := rfl

theorem coordinateCycle_unit : coordinateCycle (unit : Carrier F) = unit := by
  apply Prod.ext
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem coordinateCycle_norm (x : Carrier F) : norm (coordinateCycle x) = norm x := by
  dsimp [norm, coordinateCycle]
  rw [← SplitOctonion.trace_mul_cyclic]
  ring

theorem coordinateCycle_map {R : Type*} [CommRing R] (f : F →+* R) (x : Carrier F) :
    coordinateCycle (map f x) = map f (coordinateCycle x) := by
  apply Prod.ext
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

end Atlas.Albert

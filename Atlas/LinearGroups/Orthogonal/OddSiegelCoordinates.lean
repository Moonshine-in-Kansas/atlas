import Atlas.LinearGroups.Orthogonal.ElementaryNormal
import Atlas.LinearGroups.Orthogonal.Radical

/-! Literal coordinate Siegel elements for the original odd quadratic space.
The unhalved polar form is used, so all field characteristics are retained. -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable (r : ℕ) (F : Type*) [Field F]

def oddLong (i j : Fin r) (hij : i ≠ j) (t : F) : O_B r F :=
  siegelElement (formB r F) (e i,0) (t • (f j,0))
    (by simp [e]) (by
      simp [-QuadraticMap.polarBilin_apply_apply, polarB_apply, e, f,
        polarD_apply, Pi.single_apply, hij, Ne.symm hij])

def oddShortUpper (i : Fin r) (t : F) : O_B r F :=
  siegelElement (formB r F) (e i,0) (0,t)
    (by simp [e]) (by simp [-QuadraticMap.polarBilin_apply_apply, polarB_apply])

def oddShortLower (i : Fin r) (t : F) : O_B r F :=
  siegelElement (formB r F) (f i,0) (0,-t)
    (by simp [f]) (by simp [-QuadraticMap.polarBilin_apply_apply, polarB_apply])

theorem oddLong_apply (i j : Fin r) (hij : i ≠ j) (t : F) (v : VectorB r F) :
    (oddLong r F i j hij t).val v =
      v + (Pi.single (.inl i) (t*v.1 (.inl j)),0) -
        (Pi.single (.inr j) (t*v.1 (.inr i)),0) := by
  change siegel (formB r F) (e i,0) (t • (f j,0)) v = _
  rw [show t • ((f j,0) : VectorB r F) = (t • f j,0) by simp]
  have hp : (formB r F).polarBilin v (t • f j,0) = t*v.1 (.inl j) := by
    rw [polarB_apply]
    simp [-QuadraticMap.polarBilin_apply_apply]
  have hu : (formB r F).polarBilin v (e i,0) = v.1 (.inr i) := by
    rw [polarB_apply, polarD_e]
    simp
  have hq : formB r F (t • f j,0) = 0 := by simp [f]
  rw [siegel, hp, hu, hq, zero_mul, zero_smul, sub_zero]
  apply Prod.ext
  · funext k
    cases k <;> simp [e, f, Pi.single_apply] <;> split_ifs <;> ring
  · simp

theorem oddShortUpper_apply (i : Fin r) (t : F) (v : VectorB r F) :
    (oddShortUpper r F i t).val v =
      v + (Pi.single (.inl i) (2*t*v.2-t^2*v.1 (.inr i) : F),0) -
        (0,t*v.1 (.inr i)) := by
  change siegel (formB r F) (e i,0) (0,t) v = _
  have hp : (formB r F).polarBilin v (0,t) = 2*v.2*t := by
    rw [polarB_apply]
    simp [-QuadraticMap.polarBilin_apply_apply]
  have hu : (formB r F).polarBilin v (e i,0) = v.1 (.inr i) := by
    rw [polarB_apply, polarD_e]
    simp
  have hq : formB r F (0,t) = t^2 := by simp
  rw [siegel, hp, hu, hq]
  apply Prod.ext
  · funext k
    cases k <;> simp [e, Pi.single_apply] <;> split_ifs <;> ring
  · simp <;> ring

theorem oddShortLower_apply (i : Fin r) (t : F) (v : VectorB r F) :
    (oddShortLower r F i t).val v =
      v - (Pi.single (.inr i) (2*t*v.2+t^2*v.1 (.inl i) : F),0) +
        (0,t*v.1 (.inl i)) := by
  change siegel (formB r F) (f i,0) (0,-t) v = _
  have hp : (formB r F).polarBilin v (0,-t) = -(2*v.2*t) := by
    rw [polarB_apply]
    simp [-QuadraticMap.polarBilin_apply_apply]
  have hu : (formB r F).polarBilin v (f i,0) = v.1 (.inl i) := by
    rw [polarB_apply, polarD_f]
    simp
  have hq : formB r F (0,-t) = t^2 := by simp
  rw [siegel, hp, hu, hq]
  apply Prod.ext
  · funext k
    cases k <;> simp [f, Pi.single_apply] <;> split_ifs <;> ring
  · simp <;> ring

@[simp] theorem oddLong_apply_x (i j : Fin r) (hij : i ≠ j) (t : F)
    (v : VectorB r F) (k : Fin r) :
    ((oddLong r F i j hij t).val v).1 (.inl k) =
      v.1 (.inl k) + if i=k then t*v.1 (.inl j) else 0 := by
  simp [oddLong_apply, Pi.single_apply, eq_comm]

@[simp] theorem oddLong_apply_y (i j : Fin r) (hij : i ≠ j) (t : F)
    (v : VectorB r F) (k : Fin r) :
    ((oddLong r F i j hij t).val v).1 (.inr k) =
      v.1 (.inr k) - if j=k then t*v.1 (.inr i) else 0 := by
  simp [oddLong_apply, Pi.single_apply, eq_comm]

@[simp] theorem oddLong_apply_z (i j : Fin r) (hij : i ≠ j) (t : F)
    (v : VectorB r F) : ((oddLong r F i j hij t).val v).2 = v.2 := by
  simp [oddLong_apply]

@[simp] theorem oddShortUpper_apply_x (i : Fin r) (t : F)
    (v : VectorB r F) (k : Fin r) :
    ((oddShortUpper r F i t).val v).1 (.inl k) =
      v.1 (.inl k) + if i=k then 2*t*v.2-t^2*v.1 (.inr i) else 0 := by
  simp [oddShortUpper_apply, Pi.single_apply, eq_comm]

@[simp] theorem oddShortUpper_apply_y (i : Fin r) (t : F)
    (v : VectorB r F) (k : Fin r) :
    ((oddShortUpper r F i t).val v).1 (.inr k) = v.1 (.inr k) := by
  simp [oddShortUpper_apply, Pi.single_apply, eq_comm]

@[simp] theorem oddShortUpper_apply_z (i : Fin r) (t : F) (v : VectorB r F) :
    ((oddShortUpper r F i t).val v).2 = v.2-t*v.1 (.inr i) := by
  simp [oddShortUpper_apply]

@[simp] theorem oddShortLower_apply_x (i : Fin r) (t : F)
    (v : VectorB r F) (k : Fin r) :
    ((oddShortLower r F i t).val v).1 (.inl k) = v.1 (.inl k) := by
  simp [oddShortLower_apply, Pi.single_apply, eq_comm]

@[simp] theorem oddShortLower_apply_y (i : Fin r) (t : F)
    (v : VectorB r F) (k : Fin r) :
    ((oddShortLower r F i t).val v).1 (.inr k) =
      v.1 (.inr k) - if i=k then 2*t*v.2+t^2*v.1 (.inl i) else 0 := by
  simp [oddShortLower_apply, Pi.single_apply, eq_comm]

@[simp] theorem oddShortLower_apply_z (i : Fin r) (t : F) (v : VectorB r F) :
    ((oddShortLower r F i t).val v).2 = v.2+t*v.1 (.inl i) := by
  simp [oddShortLower_apply]

theorem oddLong_mem_elementary (i j : Fin r) (hij : i ≠ j) (t : F) :
    oddLong r F i j hij t ∈ elementarySubgroup (formB r F) :=
  siegelElement_mem _ _ _ _ _

theorem oddShortUpper_mem_elementary (i : Fin r) (t : F) :
    oddShortUpper r F i t ∈ elementarySubgroup (formB r F) :=
  siegelElement_mem _ _ _ _ _

theorem oddShortLower_mem_elementary (i : Fin r) (t : F) :
    oddShortLower r F i t ∈ elementarySubgroup (formB r F) :=
  siegelElement_mem _ _ _ _ _

end Atlas.Orthogonal

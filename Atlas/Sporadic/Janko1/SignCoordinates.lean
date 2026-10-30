import Atlas.Sporadic.Janko1.CoordinateRepresentation

/-! The three-dimensional binary space of diagonal sign changes. -/
namespace Atlas.Janko1

abbrev SignParameters := Fin 3 → ZMod 2

def signBit (j : Fin 3) (t : Fin 7) : ZMod 2 :=
  if t - (j.castLE (by decide) : Fin 7) = 0 ∨ t - (j.castLE (by decide) : Fin 7) = 3 ∨
    t - (j.castLE (by decide) : Fin 7) = 5 ∨ t - (j.castLE (by decide) : Fin 7) = 6 then 1 else 0

def signCharacter (a : SignParameters) (t : Fin 7) : Field :=
  (-1 : Field) ^ (a 0 * signBit 0 t + a 1 * signBit 1 t + a 2 * signBit 2 t).val

def signFactor (a : SignParameters) : Fin 8 → Field := Fin.cons 1 (signCharacter a)

set_option maxRecDepth 8192 in
theorem signCharacter_add : ∀ (a b : SignParameters) (t : Fin 7),
    signCharacter (a+b) t = signCharacter a t * signCharacter b t := by decide

set_option maxRecDepth 8192 in
theorem signCharacter_zero : ∀ t : Fin 7, signCharacter 0 t = 1 := by decide

set_option maxRecDepth 8192 in
theorem signCharacter_square : ∀ (a : SignParameters) (t : Fin 7),
    signCharacter a t * signCharacter a t = 1 := by decide

theorem signFactor_add (a b : SignParameters) (i : Fin 8) :
    signFactor (a+b) i = signFactor a i * signFactor b i := by
  refine Fin.cases ?_ (fun t => ?_) i
  · simp [signFactor]
  · exact signCharacter_add a b t

theorem signFactor_zero (i : Fin 8) : signFactor 0 i = 1 := by
  refine Fin.cases ?_ (fun t => ?_) i
  · rfl
  · exact signCharacter_zero t

theorem signFactor_square (a : SignParameters) (i : Fin 8) :
    signFactor a i * signFactor a i = 1 := by
  refine Fin.cases ?_ (fun t => ?_) i
  · simp [signFactor]
  · exact signCharacter_square a t

def signCoordinates (a : SignParameters) : (Fin 8 → Field) →ₗ[Field] (Fin 8 → Field) where
  toFun x i := signFactor a i * x i
  map_add' x y := by funext i; simp [mul_add]
  map_smul' c x := by funext i; simp [mul_left_comm]

def signLinear (a : SignParameters) : Module.End Field (SplitOctonion.Carrier Field) :=
  wilsonEquiv.toLinearMap.comp ((signCoordinates a).comp wilsonEquiv.symm.toLinearMap)

theorem signLinear_zero : signLinear 0 = 1 := by
  apply LinearMap.ext
  intro x
  simp [signLinear, signCoordinates, signFactor_zero]

theorem signLinear_add (a b : SignParameters) :
    signLinear (a+b) = signLinear a * signLinear b := by
  apply LinearMap.ext
  intro x
  simp only [signLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Module.End.mul_apply, LinearEquiv.symm_apply_apply]
  congr 1
  funext i
  exact (congrArg (fun c => c * (wilsonEquiv.symm x) i) (signFactor_add a b i)).trans
    (mul_assoc (signFactor a i) (signFactor b i) _)

theorem signLinear_square (a : SignParameters) : signLinear a * signLinear a = 1 := by
  rw [← signLinear_add]
  have h : a+a = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (a i)
  rw [h, signLinear_zero]

theorem signLinear_coordinates (a : SignParameters) (x : Fin 8 → Field) :
    signLinear a (wilsonEquiv x) = wilsonEquiv (signCoordinates a x) := by
  simp [signLinear]

set_option maxRecDepth 8192 in
theorem signCharacter_injective : Function.Injective signCharacter := by decide

theorem signLinear_injective : Function.Injective signLinear := by
  intro a b h
  apply signCharacter_injective
  funext t
  have he := congrArg (fun f : Module.End Field (SplitOctonion.Carrier Field) =>
    wilsonEquiv.symm (f (wilsonEquiv (Pi.single t.succ 1))) t.succ) h
  simp only [signLinear_coordinates, LinearEquiv.symm_apply_apply] at he
  simpa [signCoordinates, signFactor] using he

end Atlas.Janko1

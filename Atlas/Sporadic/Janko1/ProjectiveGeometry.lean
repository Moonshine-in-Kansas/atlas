import Atlas.Sporadic.Janko1.Local168
import Atlas.LinearAlgebra.ProjectiveConeCount
import Mathlib.LinearAlgebra.Projectivization.Action

/-!
Source-only candidate. Actual projective lines in the installed trace-zero
octonions, with their induced G2(F11) action and Wilson-coordinate dictionary.
The verified H normal form is reused. No whole-J1 order or stabilizer is assumed.
-/
noncomputable section
namespace Atlas.Janko1

/-- Restriction of the existing octonion automorphism, not a new representation model. -/
def imaginaryRepresentation : G2.Model Field →* (Imaginary ≃ₗ[Field] Imaginary) where
  toFun g :=
    { toFun x := ⟨g.val x.val, by
        change SplitOctonion.trace (g.val x.val) = 0
        exact (SplitOctonion.automorphism_trace g x.val).trans x.property⟩
      invFun x := ⟨(g⁻¹).val x.val, by
        change SplitOctonion.trace ((g⁻¹).val x.val) = 0
        exact (SplitOctonion.automorphism_trace (g⁻¹) x.val).trans x.property⟩
      left_inv x := Subtype.ext (g.val.symm_apply_apply x.val)
      right_inv x := Subtype.ext (g.val.apply_symm_apply x.val)
      map_add' x y := Subtype.ext (map_add g.val x.val y.val)
      map_smul' c x := Subtype.ext (map_smul g.val c x.val) }
  map_one' := by ext x; rfl
  map_mul' g h := by ext x; rfl

theorem imaginaryRepresentation_apply (g : G2.Model Field) (x : Imaginary) :
    (imaginaryRepresentation g x).val = g.val x.val := rfl

theorem imaginaryRepresentation_norm (g : G2.Model Field) (x : Imaginary) :
    imaginaryNorm (imaginaryRepresentation g x) = imaginaryNorm x :=
  SplitOctonion.automorphism_norm g x.val

abbrev ProjV := Projectivization Field Imaginary

instance projectiveAction : MulAction (G2.Model Field) ProjV :=
  MulAction.compHom ProjV imaginaryRepresentation

/-- Wilson coordinates of the actual restricted octonion action. -/
def imaginaryCoordinateAction (g : G2.Model Field) :
    (Fin 7 → Field) ≃ₗ[Field] (Fin 7 → Field) :=
  imaginaryEquivFin7.symm.trans ((imaginaryRepresentation g).trans imaginaryEquivFin7)

private theorem imaginaryCoordinateAction_coordinates (g : G2.Model Field)
    (v : Fin 7 → Field) (k : Fin 7) :
    imaginaryCoordinateAction g v k =
      (wilsonEquiv.symm (g.val (wilsonEquiv (Fin.cons 0 v)))) k.succ := rfl

theorem imaginaryCoordinateAction_one (v : Fin 7 → Field) :
    imaginaryCoordinateAction 1 v = v := by
  simp [imaginaryCoordinateAction]

theorem imaginaryCoordinateAction_mul (g h : G2.Model Field) (v : Fin 7 → Field) :
    imaginaryCoordinateAction (g * h) v =
      imaginaryCoordinateAction g (imaginaryCoordinateAction h v) := by
  simp only [imaginaryCoordinateAction, LinearEquiv.trans_apply, map_mul,
    LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply]

theorem imaginaryCoordinateAction_pow (g : G2.Model Field) (n : ℕ)
    (v : Fin 7 → Field) :
    imaginaryCoordinateAction (g ^ n) v = (imaginaryCoordinateAction g)^[n] v := by
  induction n with
  | zero => simpa using imaginaryCoordinateAction_one v
  | succ n ih =>
    rw [pow_succ', imaginaryCoordinateAction_mul, ih, Function.iterate_succ_apply']

theorem imaginaryCoordinateAction_generator (g : Fin 4) (v : Fin 7 → Field)
    (k : Fin 7) :
    imaginaryCoordinateAction (generator g) v k =
      Matrix.mulVec (imaginaryGeneratorMatrix g) v k := by
  rw [imaginaryCoordinateAction_coordinates]
  change (wilsonEquiv.symm
    (generatorLinear g (wilsonEquiv (Fin.cons 0 v)))) k.succ = _
  have hc := congrArg wilsonEquiv.symm (generatorLinear_coordinates g (Fin.cons 0 v))
  rw [wilsonEquiv.symm_apply_apply] at hc
  rw [hc]
  simp [generatorCoordinates, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    generatorMatrix, Fin.sum_univ_succ]

def coordinateShift (v : Fin 7 → Field) (k : Fin 7) : Field := v (k - 1)
def coordinateDouble (v : Fin 7 → Field) (k : Fin 7) : Field := v (4 * k)

theorem imaginaryCoordinateAction_P (v : Fin 7 → Field) :
    imaginaryCoordinateAction P v = coordinateShift v := by
  funext k
  change imaginaryCoordinateAction (generator 0) v k = _
  rw [imaginaryCoordinateAction_generator]
  fin_cases k <;>
    simp [coordinateShift, imaginaryGeneratorMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
  exact congrArg v (by decide : (6 : Fin 7) = -1)

theorem imaginaryCoordinateAction_Q (v : Fin 7 → Field) :
    imaginaryCoordinateAction Q v = coordinateDouble v := by
  funext k
  change imaginaryCoordinateAction (generator 1) v k = _
  rw [imaginaryCoordinateAction_generator]
  fin_cases k <;>
    simp [coordinateDouble, imaginaryGeneratorMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem imaginaryCoordinateAction_sign (a : SignParameters) (v : Fin 7 → Field) :
    imaginaryCoordinateAction (signElement a) v = fun k => signCharacter a k * v k := by
  funext k
  rw [imaginaryCoordinateAction_coordinates]
  change (wilsonEquiv.symm (signLinear a (wilsonEquiv (Fin.cons 0 v)))) k.succ = _
  rw [signLinear_coordinates, wilsonEquiv.symm_apply_apply]
  rfl

/-- At most six shifts, two doublings, and one diagonal sign change. -/
def hCoordinateAction (t : SignParameters × (Fin 7 × Fin 3))
    (v : Fin 7 → Field) (k : Fin 7) : Field :=
  signCharacter t.1 k * (coordinateShift^[t.2.1.val]
    (coordinateDouble^[t.2.2.val] v)) k

theorem imaginaryCoordinateAction_normalForm (t : SignParameters × (Fin 7 × Fin 3))
    (v : Fin 7 → Field) :
    imaginaryCoordinateAction (hNormalFormEquiv t : G2.Model Field) v =
      hCoordinateAction t v := by
  rw [hNormalFormEquiv_apply, imaginaryCoordinateAction_mul,
    imaginaryCoordinateAction_mul, imaginaryCoordinateAction_pow,
    imaginaryCoordinateAction_pow, imaginaryCoordinateAction_sign]
  rw [show (imaginaryCoordinateAction P : (Fin 7 → Field) → (Fin 7 → Field)) =
    coordinateShift from funext imaginaryCoordinateAction_P]
  rw [show (imaginaryCoordinateAction Q : (Fin 7 → Field) → (Fin 7 → Field)) =
    coordinateDouble from funext imaginaryCoordinateAction_Q]
  rfl

/-- A genuine one-dimensional subspace of Imaginary, in Wilson coordinates. -/
def coordinatePoint (v : Fin 7 → Field) (hv : v ≠ 0) : ProjV :=
  Projectivization.mk Field (imaginaryEquivFin7.symm v)
    (by simpa using imaginaryEquivFin7.symm.injective.ne hv)

theorem coordinatePoint_eq_iff (v w : Fin 7 → Field) (hv : v ≠ 0) (hw : w ≠ 0) :
    coordinatePoint v hv = coordinatePoint w hw ↔ ∃ c : Field, c • w = v := by
  rw [coordinatePoint, coordinatePoint, Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by simpa using congrArg imaginaryEquivFin7 hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by simpa using congrArg imaginaryEquivFin7.symm hc⟩

theorem coordinatePoint_smul (g : G2.Model Field) (v : Fin 7 → Field) (hv : v ≠ 0) :
    g • coordinatePoint v hv = coordinatePoint (imaginaryCoordinateAction g v)
      (by simpa using (imaginaryCoordinateAction g).injective.ne hv) := by
  change imaginaryRepresentation g •
    Projectivization.mk Field (imaginaryEquivFin7.symm v) _ =
      Projectivization.mk Field (imaginaryEquivFin7.symm (imaginaryCoordinateAction g v)) _
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  simp only [one_smul, imaginaryCoordinateAction, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.smul_def]

theorem imaginaryNorm_smul (c : Field) (x : Imaginary) :
    imaginaryNorm (c • x) = c ^ 2 * imaginaryNorm x := by
  simp only [imaginaryNorm_coordinates, map_smul, Pi.smul_apply, smul_eq_mul,
    mul_pow, Finset.mul_sum]

theorem imaginaryNorm_unit_smul_iff (c : Fieldˣ) (x : Imaginary) :
    imaginaryNorm (c • x) = 0 ↔ imaginaryNorm x = 0 := by
  rw [Units.smul_def, imaginaryNorm_smul]
  simp [c.ne_zero]

def IsIsotropic (p : ProjV) : Prop := imaginaryNorm p.rep = 0

theorem isIsotropic_mk (x : Imaginary) (hx : x ≠ 0) :
    IsIsotropic (Projectivization.mk Field x hx) ↔ imaginaryNorm x = 0 :=
  Atlas.LinearAlgebra.cone_mk_iff (fun x : Imaginary => imaginaryNorm x = 0)
    imaginaryNorm_unit_smul_iff x hx

theorem isIsotropic_coordinatePoint (v : Fin 7 → Field) (hv : v ≠ 0) :
    IsIsotropic (coordinatePoint v hv) ↔ ∑ k : Fin 7, v k ^ 2 = 0 := by
  rw [coordinatePoint, isIsotropic_mk, imaginaryNorm_coordinates,
    imaginaryEquivFin7.apply_symm_apply]

theorem isIsotropic_smul_iff (g : G2.Model Field) (p : ProjV) :
    IsIsotropic (g • p) ↔ IsIsotropic p := by
  induction p using Projectivization.ind with
  | h x hx =>
    change IsIsotropic (imaginaryRepresentation g • Projectivization.mk Field x hx) ↔ _
    rw [Projectivization.smul_mk, isIsotropic_mk, isIsotropic_mk]
    change imaginaryNorm (imaginaryRepresentation g x) = 0 ↔ imaginaryNorm x = 0
    rw [imaginaryRepresentation_norm]

end Atlas.Janko1

import Atlas.Algebra.Albert.CubicPolarization

/-! Coordinate dictionary for Wilson, “A simple construction of the Ree groups
of type ²F₄”, draft 05/06/09, sections 1–2. In each block the nine indices denote
-4,-3,-2,-1,0,1,2,3,4. The eight octonion coordinates retain their existing order.
The equations below hold over coefficient rings, not just as finite-field functions. -/
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F]

abbrev WilsonCoordinates (F : Type*) := Fin 3 → Fin 9 → F

def wilsonCoordinatesEquiv : Carrier F ≃ₗ[F] WilsonCoordinates F where
  toFun x i := ![x.2 i 0, x.2 i 1, x.2 i 2, x.2 i 3, x.1 i,
    x.2 i 4, x.2 i 5, x.2 i 6, x.2 i 7]
  invFun w := (fun i => w i 4, fun i =>
    ![w i 0, w i 1, w i 2, w i 3, w i 5, w i 6, w i 7, w i 8])
  left_inv x := by
    apply Prod.ext
    · rfl
    · funext i j; fin_cases j <;> rfl
  right_inv w := by funext i j; fin_cases j <;> rfl
  map_add' x y := by funext i j; fin_cases j <;> rfl
  map_smul' a x := by funext i j; fin_cases j <;> rfl

def wilsonTrace (w : WilsonCoordinates F) : F := w 0 4 + w 1 4 + w 2 4

def wilsonTraceLinear : WilsonCoordinates F →ₗ[F] F where
  toFun := wilsonTrace
  map_add' x y := by simp [wilsonTrace]; ring
  map_smul' a x := by simp [wilsonTrace]; ring

def wilsonBlockNorm (w : Fin 9 → F) : F :=
  w 0*w 8 + w 1*w 7 + w 2*w 6 + w 3*w 5

def wilsonQuadratic (w : WilsonCoordinates F) : F :=
  w 0 4*w 1 4 + w 0 4*w 2 4 + w 1 4*w 2 4 +
    wilsonBlockNorm (w 0) + wilsonBlockNorm (w 1) + wilsonBlockNorm (w 2)

/-- The cyclic orbit of one of the ten signed triples in Wilson's cubic. -/
def wilsonTriple (w : WilsonCoordinates F) (i j k : Fin 9) : F :=
  w 0 i*w 1 j*w 2 k + w 0 j*w 1 k*w 2 i + w 0 k*w 1 i*w 2 j

def wilsonCubic (w : WilsonCoordinates F) : F :=
  wilsonTriple w 5 2 6 + wilsonTriple w 3 6 2 +
  wilsonTriple w 5 1 7 + wilsonTriple w 3 7 1 +
  wilsonTriple w 5 8 0 + wilsonTriple w 3 0 8 +
  wilsonTriple w 0 6 7 + wilsonTriple w 8 2 1 +
  wilsonTriple w 0 7 6 + wilsonTriple w 8 1 2 +
  w 0 3*w 1 3*w 2 3 + w 0 4*w 1 4*w 2 4 + w 0 5*w 1 5*w 2 5 +
  w 0 4*wilsonBlockNorm (w 0) + w 1 4*wilsonBlockNorm (w 1) +
  w 2 4*wilsonBlockNorm (w 2)

@[simp] theorem wilsonTrace_coordinates (x : Carrier F) :
    wilsonTrace (wilsonCoordinatesEquiv x) = trace x := rfl

def wilsonTraceZeroEquiv : TraceZero F ≃ₗ[F] (wilsonTraceLinear (F:=F)).ker where
  toFun w := ⟨wilsonCoordinatesEquiv (w : Carrier F), w.property⟩
  invFun w := ⟨(wilsonCoordinatesEquiv (F:=F)).symm (w : WilsonCoordinates F), by
    change trace ((wilsonCoordinatesEquiv (F:=F)).symm (w : WilsonCoordinates F)) = 0
    rw [← wilsonTrace_coordinates, LinearEquiv.apply_symm_apply]
    exact w.property⟩
  left_inv w := by
    apply Subtype.ext
    exact wilsonCoordinatesEquiv.symm_apply_apply (w : Carrier F)
  right_inv w := by
    apply Subtype.ext
    exact wilsonCoordinatesEquiv.apply_symm_apply (w : WilsonCoordinates F)
  map_add' u v := by
    apply Subtype.ext
    exact wilsonCoordinatesEquiv.map_add (u : Carrier F) (v : Carrier F)
  map_smul' a w := by
    apply Subtype.ext
    exact wilsonCoordinatesEquiv.map_smul a (w : Carrier F)

def wilsonPolar (u v : WilsonCoordinates F) : F :=
  wilsonQuadratic (u+v) + wilsonQuadratic u + wilsonQuadratic v

def wilsonTrilinear (u v w : WilsonCoordinates F) : F :=
  wilsonCubic (u+v+w) + wilsonCubic (u+v) + wilsonCubic (u+w) +
    wilsonCubic (v+w) + wilsonCubic u + wilsonCubic v + wilsonCubic w

variable [CharP F 2]

theorem wilsonQuadratic_coordinates (x : Carrier F) :
    wilsonQuadratic (wilsonCoordinatesEquiv x) = quadraticTrace x := by
  simp [wilsonQuadratic, wilsonBlockNorm, wilsonCoordinatesEquiv, quadraticTrace,
    Atlas.SplitOctonion.norm, sub_eq_add_neg, CharTwo.neg_eq]
  ring

-- Checking the displayed 45 monomials requires expansion of the fixed octonion table.
set_option maxHeartbeats 800000 in
theorem wilsonCubic_coordinates (x : Carrier F) :
    wilsonCubic (wilsonCoordinatesEquiv x) = Atlas.Albert.norm x := by
  simp [wilsonCubic, wilsonTriple, wilsonBlockNorm, wilsonCoordinatesEquiv, Atlas.Albert.norm,
    Atlas.SplitOctonion.norm, Atlas.SplitOctonion.trace, Atlas.SplitOctonion.mul,
    sub_eq_add_neg, CharTwo.neg_eq]
  ring

theorem wilson_traceZero_iff (x : Carrier F) :
    wilsonTrace (wilsonCoordinatesEquiv x) = 0 ↔ x ∈ TraceZero F := Iff.rfl

theorem wilsonPolar_coordinates (u v : TraceZero F) :
    wilsonPolar (wilsonCoordinatesEquiv u) (wilsonCoordinatesEquiv v) =
      traceZeroPolar u v := by
  unfold wilsonPolar
  rw [← wilsonCoordinatesEquiv.map_add, wilsonQuadratic_coordinates,
    wilsonQuadratic_coordinates, wilsonQuadratic_coordinates, traceZeroPolar_quadratic]
  simp only [traceZeroQuadratic, Submodule.coe_add, sub_eq_add_neg, CharTwo.neg_eq]

theorem wilsonTrilinear_coordinates (u v w : TraceZero F) :
    wilsonTrilinear (wilsonCoordinatesEquiv u) (wilsonCoordinatesEquiv v)
      (wilsonCoordinatesEquiv w) = traceZeroPolar (traceZeroCross u v) w := by
  unfold wilsonTrilinear
  simp only [← wilsonCoordinatesEquiv.map_add, wilsonCubic_coordinates]
  exact traceZeroCubic_fullPolarization u v w

theorem wilsonTrilinear_characterizes_cross (u v a : TraceZero F)
    (h : ∀ w : TraceZero F, traceZeroPolar a w =
      wilsonTrilinear (wilsonCoordinatesEquiv u) (wilsonCoordinatesEquiv v)
        (wilsonCoordinatesEquiv w)) : a = traceZeroCross u v := by
  apply sub_eq_zero.mp
  apply traceZeroPolar_nondegenerate
  intro w
  rw [sub_eq_add_neg, traceZeroPolar_add_left, ← neg_one_smul F (traceZeroCross u v),
    traceZeroPolar_smul_left, h, wilsonTrilinear_coordinates]
  ring

end Atlas.ReeF4

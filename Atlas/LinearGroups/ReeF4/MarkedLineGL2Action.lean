import Atlas.LinearGroups.ReeF4.WeylGL2Model
import Atlas.LinearGroups.ReeF4.SpecialMarkedLineIncidence

/-!
Uncompiled source-only checkpoint. The existing GL2 subgroup acts on the actual
marked line by its defining two-dimensional matrix representation. All coordinate
arguments use the existing block equivalence and root/torus formulas.
No group order, full-group generation, transitivity, or radical size is used.
No Lean, Lake, checker, audit, or enumeration was run for this draft.
-/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The retained marked-line parametrization, valued in the actual span. -/
def specialMarkedLineParam : (Fin 2 → F) →ₗ[F] specialMarkedLine (F := F) where
  toFun v := ⟨specialMarkedLineVector (v 0) (v 1), by
    rw [specialMarkedLineVector_eq]
    exact Submodule.mem_span_pair.mpr ⟨v 0, v 1, rfl⟩⟩
  map_add' v w := by
    apply Subtype.ext
    change specialMarkedLineVector ((v + w) 0) ((v + w) 1) =
      specialMarkedLineVector (v 0) (v 1) + specialMarkedLineVector (w 0) (w 1)
    simp only [specialMarkedLineVector_eq, Pi.add_apply, add_smul]
    exact add_add_add_comm _ _ _ _
  map_smul' a v := by
    apply Subtype.ext
    change specialMarkedLineVector ((a • v) 0) ((a • v) 1) =
      a • specialMarkedLineVector (v 0) (v 1)
    simp only [specialMarkedLineVector_eq, Pi.smul_apply, smul_eq_mul,
      smul_add, smul_smul]

theorem specialMarkedLineParam_val (v : Fin 2 → F) :
    (specialMarkedLineParam v).val = specialMarkedLineVector (v 0) (v 1) := rfl

private theorem specialMarkedLineParam_read (v : Fin 2 → F) :
    (longSL2BlocksEquiv (specialMarkedLineParam v).val).1 1 = v := by
  change (longSL2BlocksEquiv
    (longSL2BlocksEquiv.symm (specialMarkedLineCoordinates (v 0) (v 1)))).1 1 = v
  rw [LinearEquiv.apply_symm_apply]
  exact funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)

theorem specialMarkedLineParam_bijective :
    Function.Bijective (specialMarkedLineParam (F := F)) := by
  constructor
  · intro v w h
    have he := congrArg
      (fun x : specialMarkedLine (F := F) => (longSL2BlocksEquiv x.val).1 1) h
    simpa only [specialMarkedLineParam_read] using he
  · rintro ⟨w, hw⟩
    obtain ⟨a, b, he⟩ := Submodule.mem_span_pair.mp hw
    refine ⟨![a,b], Subtype.ext ?_⟩
    exact (specialMarkedLineVector_eq a b).trans he

/-- Actual coordinates on the marked two-space, not a replacement ambient model. -/
def specialMarkedLineCoordinateEquiv :
    (Fin 2 → F) ≃ₗ[F] specialMarkedLine (F := F) :=
  LinearEquiv.ofBijective specialMarkedLineParam specialMarkedLineParam_bijective

theorem specialMarkedLineCoordinateEquiv_val (v : Fin 2 → F) :
    (specialMarkedLineCoordinateEquiv v).val =
      specialMarkedLineVector (v 0) (v 1) := rfl

/-- On this particular natural block the central scalar torus has weight one. -/
theorem torusEquiv_scalar_markedLine (m : ℕ) (c : Fˣ) (a b : F) :
    torusEquiv m c c (specialMarkedLineVector a b) =
      specialMarkedLineVector ((c : F) * a) ((c : F) * b) := by
  have h0 : longSL2CentralExponent m (0,0) = 1 := rfl
  have h2 : longSL2CentralExponent m (2,0) = 1 := rfl
  simp only [specialMarkedLineVector_eq, _root_.map_add, _root_.map_smul, torusEquiv_root,
    torusWeight_scalar, h0, h2, zpow_one, smul_smul, mul_comm]

/-- The scalar/SL2 product acts as cA, matching the existing GL2 comparison map. -/
theorem modelLongSL2ProductHom_markedLine {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (A : LongSL2 (F := F)) (c : Fˣ) (v : Fin 2 → F) :
    (modelLongSL2ProductHom hcard (A,c)).val (specialMarkedLineVector (v 0) (v 1)) =
      specialMarkedLineVector
        (((Atlas.sl2ScalarGL2Equiv (A,c) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) 0)
        (((Atlas.sl2ScalarGL2Equiv (A,c) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) 1) := by
  change longSL2Representation (theta F m).toRingHom A
    (torusEquiv m c c (specialMarkedLineVector (v 0) (v 1))) = _
  rw [torusEquiv_scalar_markedLine, longSL2Representation_markedLine]
  have hmat : (Atlas.sl2ScalarGL2Equiv (A,c) : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • (A : Matrix (Fin 2) (Fin 2) F) :=
    Atlas.sl2ScalarToGL_matrix A c
  rw [hmat, Matrix.smul_mulVec, ← Matrix.mulVec_smul]
  simp only [Matrix.mulVec, Matrix.vec2_dotProduct, Pi.smul_apply, smul_eq_mul]

theorem modelLongGL2Hom_markedLine {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (B : Matrix.GeneralLinearGroup (Fin 2) F) (v : Fin 2 → F) :
    (modelLongGL2Hom hcard B).val (specialMarkedLineVector (v 0) (v 1)) =
      specialMarkedLineVector
        (((B : Matrix (Fin 2) (Fin 2) F) *ᵥ v) 0)
        (((B : Matrix (Fin 2) (Fin 2) F) *ᵥ v) 1) := by
  obtain ⟨⟨A,c⟩, rfl⟩ := (Atlas.sl2ScalarGL2Equiv (F := F)).surjective B
  rw [modelLongGL2Hom_scalar_SL2]
  exact modelLongSL2ProductHom_markedLine hcard A c v

theorem modelLongGL2Hom_maps_specialMarkedLine {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (B : Matrix.GeneralLinearGroup (Fin 2) F) {w : TraceZero F}
    (hw : w ∈ specialMarkedLine (F := F)) :
    (modelLongGL2Hom hcard B).val w ∈ specialMarkedLine (F := F) := by
  obtain ⟨v, hv⟩ := (specialMarkedLineCoordinateEquiv (F := F)).surjective ⟨w,hw⟩
  have he : specialMarkedLineVector (v 0) (v 1) = w := congrArg Subtype.val hv
  rw [← he, modelLongGL2Hom_markedLine]
  exact (specialMarkedLineParam ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ v)).property

/-- Transfer the usual matrix GL2 to the actual marked-line automorphism group. -/
def markedLineGL2ActionEquiv : Matrix.GeneralLinearGroup (Fin 2) F ≃*
    (specialMarkedLine (F := F) ≃ₗ[F] specialMarkedLine (F := F)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv
      (specialMarkedLineCoordinateEquiv (F := F))).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F (specialMarkedLine (F := F))))

theorem markedLineGL2ActionEquiv_apply
    (B : Matrix.GeneralLinearGroup (Fin 2) F) (v : Fin 2 → F) :
    markedLineGL2ActionEquiv B (specialMarkedLineCoordinateEquiv v) =
      specialMarkedLineCoordinateEquiv ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := by
  change specialMarkedLineCoordinateEquiv
    ((Matrix.GeneralLinearGroup.toLin B).toLinearEquiv
      (specialMarkedLineCoordinateEquiv.symm (specialMarkedLineCoordinateEquiv v))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end Atlas.ReeF4

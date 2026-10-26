import Atlas.LinearGroups.ReeF4.WeylSL2Model
import Atlas.LinearGroups.ReeF4.SpecialMarkedPoints

/-! The marked two-space consists of special nonzero vectors. This is proved
through the actual SL2 representation, with no isotropy assumption, point
count, full-group transitivity, or general line theorem. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
attribute [local instance] Classical.propDecidable

/-- The actual marked two-dimensional span, before any general incidence claim. -/
def specialMarkedLine : Submodule F (TraceZero F) :=
  Submodule.span F {rootVector (F := F) (0,0), rootVector (2,0)}

def specialMarkedLineCoordinates (a b : F) : LongSL2Blocks F :=
  (![0,![a,b],0,0],0,0,0,0)

def specialMarkedLineVector (a b : F) : TraceZero F :=
  longSL2BlocksEquiv.symm (specialMarkedLineCoordinates a b)

set_option maxHeartbeats 800000 in
theorem specialMarkedLineVector_eq (a b : F) :
    specialMarkedLineVector a b = a • rootVector (F := F) (0,0) + b • rootVector (2,0) := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [specialMarkedLineVector, specialMarkedLineCoordinates, longSL2BlocksEquiv,
        longSL2FromBlocks, longSL2FromBlocksFormula, rootVector, smul_eq_mul]
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp [specialMarkedLineVector, specialMarkedLineCoordinates, longSL2BlocksEquiv,
        longSL2FromBlocks, longSL2FromBlocksFormula, rootVector, Pi.single_apply,
        smul_eq_mul]

@[simp] theorem specialMarkedLineVector_first :
    specialMarkedLineVector (1 : F) 0 = rootVector (F := F) (0,0) := by
  rw [specialMarkedLineVector_eq]
  simp

/-- Explicit determinant-one matrix with first column (a,b), for any nonzero
column. The two branches expose the exact nonzero denominator assumptions. -/
def specialMarkedLineMatrix (a b : F) (h : a ≠ 0 ∨ b ≠ 0) : LongSL2 (F := F) :=
  if ha : a = 0 then
    ⟨!![0,b⁻¹; b,0], by
      have hb : b ≠ 0 := h.resolve_left (not_not.mpr ha)
      simp [Matrix.det_fin_two, hb, CharTwo.neg_eq]⟩
  else
    ⟨!![a,0; b,a⁻¹], by simp [Matrix.det_fin_two, ha]⟩

theorem specialMarkedLineMatrix_column (a b : F) (h : a ≠ 0 ∨ b ≠ 0) :
    ((specialMarkedLineMatrix a b h : Matrix (Fin 2) (Fin 2) F) 0 0 = a) ∧
    ((specialMarkedLineMatrix a b h : Matrix (Fin 2) (Fin 2) F) 1 0 = b) := by
  by_cases ha : a = 0
  · simp [specialMarkedLineMatrix, ha]
  · simp [specialMarkedLineMatrix, ha]

set_option maxHeartbeats 800000 in
theorem longSL2Representation_markedLine (σ : F →+* F) (A : LongSL2 (F := F))
    (a b : F) :
    longSL2Representation σ A (specialMarkedLineVector a b) =
      specialMarkedLineVector (A.val 0 0*a+A.val 0 1*b)
        (A.val 1 0*a+A.val 1 1*b) := by
  apply longSL2BlocksEquiv.injective
  simp only [longSL2Representation, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearEquiv.trans_apply, specialMarkedLineVector,
    LinearEquiv.apply_symm_apply]
  change longSL2BlocksAction σ A (specialMarkedLineCoordinates a b) = _
  apply Prod.ext
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp [longSL2BlocksAction, specialMarkedLineCoordinates,
        Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [longSL2BlocksAction, specialMarkedLineCoordinates]

theorem specialMarkedLineMatrix_image (m : ℕ) (a b : F) (h : a ≠ 0 ∨ b ≠ 0) :
    longSL2Representation (theta F m).toRingHom (specialMarkedLineMatrix a b h)
      (rootVector (F := F) (0,0)) = a • rootVector (F := F) (0,0) + b • rootVector (2,0) := by
  have hh := longSL2Representation_markedLine (theta F m).toRingHom
    (specialMarkedLineMatrix a b h) (1 : F) 0
  obtain ⟨h0,h1⟩ := specialMarkedLineMatrix_column a b h
  simp only [specialMarkedLineVector_first, mul_one, mul_zero, add_zero, h0, h1] at hh
  exact hh.trans (specialMarkedLineVector_eq a b)

theorem isSpecialVector_markedLine_combination {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b : F) (h : a ≠ 0 ∨ b ≠ 0) :
    IsSpecialVector m (a • rootVector (F := F) (0,0) + b • rootVector (2,0)) := by
  have hs := (isSpecialVector_firstRoot (F := F) m).map_model
    (modelLongSL2Hom hcard (specialMarkedLineMatrix a b h))
  change IsSpecialVector m
    (longSL2Representation (theta F m).toRingHom (specialMarkedLineMatrix a b h)
      (rootVector (F := F) (0,0))) at hs
  rw [specialMarkedLineMatrix_image] at hs
  exact hs

/-- Every nonzero vector of this concrete marked span is intrinsically special. -/
theorem isSpecialVector_of_mem_specialMarkedLine {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (w : TraceZero F)
    (hw : w ∈ specialMarkedLine (F := F)) (hn : w ≠ 0) :
    IsSpecialVector m w := by
  obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hw
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    have ha : a = 0 := not_not.mp (fun h' => h (Or.inl h'))
    have hb : b = 0 := not_not.mp (fun h' => h (Or.inr h'))
    apply hn
    simpa [ha,hb] using he.symm
  rw [← he]
  exact isSpecialVector_markedLine_combination hcard a b hab

end Atlas.ReeF4

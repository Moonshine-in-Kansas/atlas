import Atlas.LinearGroups.Orthogonal.Basic
import Atlas.LinearGroups.Symplectic.Basic

/-! # Six-coordinate exterior square and the actual B₂ quadratic form

Coordinates are 01, 02, 03, 12, 13, 23, in that order. The symplectic
contraction is the sum of coordinates 02 and 13. Its kernel carries exactly
our standard B₂ form under the displayed coordinate map; no scalar multiplier
or target orthogonal group is assumed.
-/
noncomputable section
namespace Atlas.Orthogonal.B2Exterior

variable {F : Type*} [CommRing F]

abbrev Four (F : Type*) := Fin 4 → F
abbrev Six (F : Type*) := Fin 6 → F

/-- The six two-by-two minors of the ordered pair of vectors. -/
def wedge (u v : Four F) : Six F :=
  ![u 0 * v 1 - u 1 * v 0, u 0 * v 2 - u 2 * v 0,
    u 0 * v 3 - u 3 * v 0, u 1 * v 2 - u 2 * v 1,
    u 1 * v 3 - u 3 * v 1, u 2 * v 3 - u 3 * v 2]

/-- The quadratic Pfaffian, not the determinant (its square). -/
def pfaffian : QuadraticForm F (Six F) :=
  QuadraticMap.proj (R := F) 0 5 - QuadraticMap.proj (R := F) 1 4 +
    QuadraticMap.proj (R := F) 2 3

@[simp] theorem pfaffian_apply (w : Six F) :
    pfaffian w = w 0 * w 5 - w 1 * w 4 + w 2 * w 3 := by
  simp [pfaffian, QuadraticMap.proj, QuadraticMap.linMulLin_apply]

/-- Symplectic contraction for the basis e₀,e₁,f₀,f₁. -/
def contraction : Six F →ₗ[F] F where
  toFun w := w 1 + w 4
  map_add' _ _ := by simp only [Pi.add_apply]; ring
  map_smul' _ _ := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem contraction_apply (w : Six F) : contraction w = w 1 + w 4 := rfl

/-- The actual ordered coordinates of the previously constructed symplectic module. -/
def symplecticCoordinates (v : Atlas.Symplectic.Vector 2 F) : Four F :=
  ![v (.inl 0), v (.inl 1), v (.inr 0), v (.inr 1)]

theorem contraction_wedge (u v : Atlas.Symplectic.Vector 2 F) :
    contraction (wedge (symplecticCoordinates u) (symplecticCoordinates v)) =
      Atlas.Symplectic.form u v := by
  simp [wedge, symplecticCoordinates, Atlas.Symplectic.form_apply, Fin.sum_univ_two]
  ring

theorem pfaffian_wedge (u v : Four F) : pfaffian (wedge u v) = 0 := by
  simp [wedge]
  ring

/-- Explicit coordinates on the contraction kernel, retaining the existing B₂ carrier. -/
def fromB : VectorB 2 F →ₗ[F] Six F where
  toFun v := ![v.1 (.inl 0), v.2, v.1 (.inl 1), v.1 (.inr 1), -v.2,
    v.1 (.inr 0)]
  map_add' u v := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' c v := by ext i; fin_cases i <;> simp

@[simp] theorem fromB_contraction (v : VectorB 2 F) : contraction (fromB v) = 0 := by
  simp [fromB]

/-- The multiplier is exactly one for these coordinate and Pfaffian conventions. -/
theorem fromB_pfaffian (v : VectorB 2 F) : pfaffian (fromB v) = formB 2 F v := by
  simp [fromB, formD_apply, Fin.sum_univ_two]
  ring

/-- All contraction-zero bivectors, with no odd-characteristic hypothesis. -/
def kernelEquiv : VectorB 2 F ≃ₗ[F] LinearMap.ker (contraction (F := F)) where
  toFun v := ⟨fromB v, fromB_contraction v⟩
  invFun w := ⟨Sum.elim ![w.val 0, w.val 2] ![w.val 5, w.val 3], w.val 1⟩
  left_inv v := by
    apply Prod.ext
    · funext i
      rcases i with i | i <;> fin_cases i <;> rfl
    · rfl
  right_inv w := by
    apply Subtype.ext
    funext i
    have hw : w.val 1 + w.val 4 = 0 := w.prop
    fin_cases i
    all_goals first | rfl | exact (eq_neg_of_add_eq_zero_right hw).symm
  map_add' u v := Subtype.ext (fromB.map_add u v)
  map_smul' c v := Subtype.ext (fromB.map_smul c v)

/-- The restriction itself, as an isometry, rather than merely an equality of orders. -/
def kernelIsometry : (formB 2 F).IsometryEquiv
    (pfaffian.comp (LinearMap.ker contraction).subtype) where
  toLinearEquiv := kernelEquiv
  map_app' := fromB_pfaffian

end Atlas.Orthogonal.B2Exterior

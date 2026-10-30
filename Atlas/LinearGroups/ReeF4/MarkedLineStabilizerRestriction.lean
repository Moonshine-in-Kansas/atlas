import Atlas.LinearGroups.ReeF4.MarkedLineGL2Action
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
Uncompiled source-only checkpoint. The full setwise stabilizer of the retained
marked span has an actual split restriction map to GL2. Its kernel is exactly
the pointwise stabilizer of that span. Every stabilizer element has a unique
kernel-times-embedded-GL2 factorization, without a factorization premise.
The kernel is not yet identified with eleven root parameters or asserted to
have order q^11 or to be solvable. No full-order or simplicity result is used.
No Lean, Lake, checker, audit, or enumeration was run for this draft.
-/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The full setwise stabilizer of the actual two-space in the intrinsic Model. -/
def markedLineStabilizer (m : ℕ) : Subgroup (Model F m) where
  carrier := {g | ∀ w : TraceZero F,
    w ∈ specialMarkedLine (F := F) ↔ g.val w ∈ specialMarkedLine (F := F)}
  one_mem' := fun _ => Iff.rfl
  mul_mem' {g h} hg hh w := (hh w).trans (hg (h.val w))
  inv_mem' {g} hg w := by
    change w ∈ specialMarkedLine (F := F) ↔ g.val.symm w ∈ specialMarkedLine (F := F)
    simpa only [LinearEquiv.apply_symm_apply] using (hg (g.val.symm w)).symm

theorem mem_markedLineStabilizer_iff (m : ℕ) (g : Model F m) :
    g ∈ markedLineStabilizer m ↔ ∀ w : TraceZero F,
      w ∈ specialMarkedLine (F := F) ↔ g.val w ∈ specialMarkedLine (F := F) := Iff.rfl

/-- Equivalently, this is the literal equality of the image submodule with the line. -/
theorem mem_markedLineStabilizer_iff_map_eq (m : ℕ) (g : Model F m) :
    g ∈ markedLineStabilizer m ↔
      (specialMarkedLine (F := F)).map g.val.toLinearMap = specialMarkedLine (F := F) := by
  constructor
  · intro hg
    apply le_antisymm
    · rintro w ⟨v, hv, rfl⟩
      exact (hg v).mp hv
    · intro w hw
      refine ⟨g.val.symm w, ?_, g.val.apply_symm_apply w⟩
      exact (hg (g.val.symm w)).mpr (by
        simpa only [LinearEquiv.apply_symm_apply] using hw)
  · intro he w
    constructor
    · intro hw
      rw [← he]
      exact ⟨w, hw, rfl⟩
    · intro hw
      have hm : g.val w ∈ (specialMarkedLine (F := F)).map g.val.toLinearMap := by
        rw [he]
        exact hw
      obtain ⟨v, hv, hvw⟩ := hm
      exact (g.val.injective hvw) ▸ hv

theorem modelLongGL2Hom_mem_markedLineStabilizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (B : Matrix.GeneralLinearGroup (Fin 2) F) :
    modelLongGL2Hom hcard B ∈ markedLineStabilizer m := by
  intro w
  constructor
  · exact modelLongGL2Hom_maps_specialMarkedLine hcard B
  · intro hw
    have hi := modelLongGL2Hom_maps_specialMarkedLine hcard B⁻¹ hw
    rw [map_inv] at hi
    change (modelLongGL2Hom hcard B).val.symm
      ((modelLongGL2Hom hcard B).val w) ∈ specialMarkedLine (F := F) at hi
    simpa only [LinearEquiv.symm_apply_apply] using hi

/-- The section is the existing concrete GL2 embedding, with its stabilizer proof. -/
def markedLineLeviSection {m : ℕ} (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Matrix.GeneralLinearGroup (Fin 2) F →* markedLineStabilizer (F := F) m :=
  (modelLongGL2Hom hcard).codRestrict (markedLineStabilizer m)
    (modelLongGL2Hom_mem_markedLineStabilizer hcard)

theorem markedLineLeviSection_val {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (B : Matrix.GeneralLinearGroup (Fin 2) F) :
    (markedLineLeviSection hcard B).val = modelLongGL2Hom hcard B := rfl

/-- Restrict an arbitrary full stabilizer element to the actual line. -/
def markedLineRestrictionLinear (m : ℕ) : markedLineStabilizer (F := F) m →*
    (specialMarkedLine (F := F) ≃ₗ[F] specialMarkedLine (F := F)) where
  toFun g := g.val.val.ofSubmodules (specialMarkedLine (F := F))
    (specialMarkedLine (F := F))
    ((mem_markedLineStabilizer_iff_map_eq m g.val).mp g.property)
  map_one' := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rfl

theorem markedLineRestrictionLinear_apply (m : ℕ)
    (g : markedLineStabilizer (F := F) m) (w : specialMarkedLine (F := F)) :
    (markedLineRestrictionLinear m g w).val = g.val.val w.val := rfl

/-- The actual matrix induced by a full line-stabilizer element. -/
def markedLineRestriction (m : ℕ) : markedLineStabilizer (F := F) m →*
    Matrix.GeneralLinearGroup (Fin 2) F :=
  (markedLineGL2ActionEquiv (F := F)).symm.toMonoidHom.comp
    (markedLineRestrictionLinear m)

theorem markedLineRestriction_section {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (B : Matrix.GeneralLinearGroup (Fin 2) F) :
    markedLineRestriction m (markedLineLeviSection hcard B) = B := by
  apply (markedLineGL2ActionEquiv (F := F)).injective
  change markedLineGL2ActionEquiv
    (markedLineGL2ActionEquiv.symm
      (markedLineRestrictionLinear m (markedLineLeviSection hcard B))) = _
  rw [MulEquiv.apply_symm_apply]
  apply LinearEquiv.ext
  intro w
  obtain ⟨v, rfl⟩ := (specialMarkedLineCoordinateEquiv (F := F)).surjective w
  apply Subtype.ext
  change (modelLongGL2Hom hcard B).val (specialMarkedLineVector (v 0) (v 1)) =
    (markedLineGL2ActionEquiv B (specialMarkedLineCoordinateEquiv v)).val
  rw [markedLineGL2ActionEquiv_apply]
  exact modelLongGL2Hom_markedLine hcard B v

theorem markedLineRestriction_surjective {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Function.Surjective (markedLineRestriction (F := F) m) :=
  fun B => ⟨markedLineLeviSection hcard B, markedLineRestriction_section hcard B⟩

theorem markedLineLeviSection_injective {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Function.Injective (markedLineLeviSection hcard) := by
  intro A B h
  have he := congrArg (markedLineRestriction m) h
  simpa only [markedLineRestriction_section] using he

/-- The actual pointwise line-fixing kernel. No radical-size assertion is attached. -/
def markedLineRestrictionKernel (m : ℕ) : Subgroup (markedLineStabilizer (F := F) m) :=
  (markedLineRestriction m).ker

theorem markedLineRestrictionKernel_normal (m : ℕ) :
    (markedLineRestrictionKernel (F := F) m).Normal :=
  inferInstanceAs (markedLineRestriction (F := F) m).ker.Normal

theorem mem_markedLineRestrictionKernel_iff (m : ℕ)
    (g : markedLineStabilizer (F := F) m) :
    g ∈ markedLineRestrictionKernel m ↔
      ∀ w ∈ specialMarkedLine (F := F), g.val.val w = w := by
  change markedLineRestriction m g = 1 ↔ _
  constructor
  · intro hg w hw
    have he := congrArg (markedLineGL2ActionEquiv (F := F)) hg
    change markedLineGL2ActionEquiv
      (markedLineGL2ActionEquiv.symm (markedLineRestrictionLinear m g)) =
        markedLineGL2ActionEquiv 1 at he
    rw [MulEquiv.apply_symm_apply, map_one] at he
    exact congrArg
      (fun e : specialMarkedLine (F := F) ≃ₗ[F] specialMarkedLine (F := F) =>
        (e ⟨w,hw⟩).val) he
  · intro hg
    have he : markedLineRestrictionLinear m g = 1 := by
      apply LinearEquiv.ext
      intro w
      apply Subtype.ext
      exact hg w.val w.property
    change markedLineGL2ActionEquiv.symm (markedLineRestrictionLinear m g) = 1
    rw [he, map_one]

/-- Every arbitrary full line stabilizer element has exactly one kernel/Levi factorization. -/
theorem markedLineStabilizer_existsUnique_kernel_levi {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (g : markedLineStabilizer (F := F) m) :
    ∃! p : markedLineRestrictionKernel (F := F) m × Matrix.GeneralLinearGroup (Fin 2) F,
      p.1.val * markedLineLeviSection hcard p.2 = g := by
  let B := markedLineRestriction m g
  let r : markedLineRestrictionKernel (F := F) m :=
    ⟨g * (markedLineLeviSection hcard B)⁻¹, by
      change markedLineRestriction m (g * (markedLineLeviSection hcard B)⁻¹) = 1
      rw [map_mul, map_inv, markedLineRestriction_section]
      exact mul_inv_cancel _⟩
  have hprod : r.val * markedLineLeviSection hcard B = g := by
    change (g * (markedLineLeviSection hcard B)⁻¹) * markedLineLeviSection hcard B = g
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨(r,B), hprod, ?_⟩
  rintro ⟨s,A⟩ hs
  have hA : A = B := by
    have he := congrArg (markedLineRestriction m) hs
    have hk : markedLineRestriction m s.val = 1 := s.property
    simpa only [map_mul, hk, markedLineRestriction_section, one_mul] using he
  apply Prod.ext
  · apply Subtype.ext
    rw [hA] at hs
    exact mul_right_cancel (hs.trans hprod.symm)
  · exact hA

end Atlas.ReeF4

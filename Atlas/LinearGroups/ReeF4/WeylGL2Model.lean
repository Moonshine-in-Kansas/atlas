import Atlas.LinearGroups.SL2ScalarGL2
import Atlas.LinearGroups.ReeF4.WeylSL2Product

/-! Concrete GL₂ interpretation of the actual scalar-times-SL₂ subgroup.
This does not identify a full line stabilizer. -/
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def modelLongGL2Equiv {m : ℕ} (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Matrix.GeneralLinearGroup (Fin 2) F ≃* modelLongSL2ProductSubgroup hcard :=
  (Atlas.sl2ScalarGL2Equiv (F := F)).symm.trans (modelLongSL2ProductEquiv hcard)

def modelLongGL2Hom {m : ℕ} (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Matrix.GeneralLinearGroup (Fin 2) F →* Model F m :=
  (modelLongSL2ProductSubgroup hcard).subtype.comp (modelLongGL2Equiv hcard).toMonoidHom

theorem modelLongGL2Hom_injective {m : ℕ} (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Function.Injective (modelLongGL2Hom hcard) :=
  Subtype.val_injective.comp (modelLongGL2Equiv hcard).injective

theorem modelLongGL2Hom_scalar_SL2 {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (A : LongSL2 (F := F)) (c : Fˣ) :
    modelLongGL2Hom hcard (Atlas.sl2ScalarGL2Equiv (A,c)) =
      modelLongSL2ProductHom hcard (A,c) := by
  change ((modelLongSL2ProductEquiv hcard)
    (Atlas.sl2ScalarGL2Equiv.symm (Atlas.sl2ScalarGL2Equiv (A,c)))).val = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end Atlas.ReeF4

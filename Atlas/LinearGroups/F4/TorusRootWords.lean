import Atlas.LinearGroups.F4.TorusWeylWords

/-! Actual coroot words and their root-generated membership. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

attribute [local irreducible] simplePositive simpleNegative

/-- Uniform actual root-word identity, including characteristics two and three. -/
theorem simpleCorootWord_eq_diagonalTorus (j : Fin 4) (a : Fˣ) :
    simpleCorootWord j a=diagonalTorus (simpleCorootParameters j a) := by
  have hp : simplePositive (F:=F) j (-1)=(simplePositive j 1)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [simplePositive_add,neg_add_cancel,simplePositive_zero]
  have hn : simpleNegative (F:=F) j (-1)=(simpleNegative j 1)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [simpleNegative_add,neg_add_cancel,simpleNegative_zero]
  have hc : simpleCorootWord j a*(simplePositive j 1*simpleNegative j 1*simplePositive j 1)=
      simplePositive j (a : F)*simpleNegative j ((a⁻¹ : Fˣ) : F)*simplePositive j (a : F) := by
    simp [simpleCorootWord,hp,hn,mul_assoc]
  exact mul_right_cancel (hc.trans (simpleWeyl_factorization j a))

theorem simpleCoroot_mem_rootGenerated (j : Fin 4) (a : Fˣ) :
    diagonalTorus (simpleCorootParameters j a)∈rootGenerated := by
  rw [←simpleCorootWord_eq_diagonalTorus]
  exact simpleCorootWord_mem_rootGenerated j a

end Atlas.F4

import Atlas.LinearGroups.ReeF4.WeylSL2Weyl
import Atlas.LinearGroups.ReeF4.LongRootDerived
import Atlas.LinearGroups.ReeF4.WeylModel

/-! The actual long-root Weyl operator is a product of three elementary root
operators. No SL₂ perfectness, simplicity or order result is used. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Upper(1) Lower(1) Upper(1) is the concrete Weyl matrix in characteristic two. -/
theorem longSL2_weyl_root_word :
    longSL2Upper (1:F) * (longSL2Weyl * longSL2Upper (1:F) * longSL2Weyl) *
      longSL2Upper (1:F) = longSL2Weyl := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longSL2Weyl,longSL2Upper,Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.single,Matrix.one_apply,
      CharTwo.add_self_eq_zero,CharTwo.two_eq_zero]

theorem weylSigma_root_word (m : ℕ) :
    (longRootEquiv : TraceZero F ≃ₗ[F] TraceZero F) *
      (weylSigma * longRootEquiv * weylSigma) * longRootEquiv = weylSigma := by
  have hu : longSL2Representation (theta F m).toRingHom (longSL2Upper (1:F)) =
      longRootEquiv := by
    rw [longSL2Representation_upper]
    change longSL2ParameterHom (theta F m).toRingHom (Multiplicative.ofAdd (1:F)) = _
    exact longSL2ParameterHom_at_one _
  have h := congrArg (longSL2Representation (theta F m).toRingHom)
    (longSL2_weyl_root_word (F := F))
  simpa only [map_mul,longSL2Representation_weyl,hu] using h

def weylSigmaModel (m : ℕ) : Model F m :=
  ⟨weylSigma,weylOperator_mem_modelSubgroup m 1⟩

private theorem weylSigmaModel_val (m : ℕ) :
    (weylSigmaModel (F := F) m).val = weylSigma := rfl

private theorem longRootModel_val {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    (modelLongSL2RootHom hcard (Multiplicative.ofAdd (1:F))).val = longRootEquiv :=
  longSL2ParameterHom_at_one _

theorem weylSigmaModel_inv (m : ℕ) : (weylSigmaModel (F := F) m)⁻¹ = weylSigmaModel m := by
  apply Subtype.ext
  simp only [Subgroup.coe_inv,weylSigmaModel_val]
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_two] using weylSigma_square (F := F)

theorem weylSigmaModel_root_word {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    modelLongSL2RootHom hcard (Multiplicative.ofAdd (1:F)) *
      (weylSigmaModel m * modelLongSL2RootHom hcard (Multiplicative.ofAdd (1:F)) *
        weylSigmaModel m) *
      modelLongSL2RootHom hcard (Multiplicative.ofAdd (1:F)) = weylSigmaModel m := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul,longRootModel_val,weylSigmaModel_val]
  exact weylSigma_root_word m

theorem weylSigmaModel_mem_commutator {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (hm : 1 ≤ m) :
    weylSigmaModel (F := F) m ∈ commutator (Model F m) := by
  have hu := modelLongSL2RootHom_mem_commutator hcard hm (1:F)
  have hc := (inferInstance : (commutator (Model F m)).Normal).conj_mem _ hu (weylSigmaModel m)
  rw [weylSigmaModel_inv] at hc
  rw [←weylSigmaModel_root_word hcard]
  exact (commutator (Model F m)).mul_mem
    ((commutator (Model F m)).mul_mem hu hc) hu

end Atlas.ReeF4

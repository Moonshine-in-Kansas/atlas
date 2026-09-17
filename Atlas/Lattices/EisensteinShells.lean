import Atlas.Lattices.EisensteinComparisonLattice
import Atlas.Lattices.LeechFullIsometries
import Atlas.Lattices.LeechShortShellCounts
import Atlas.Lattices.LeechMinimum

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra

abbrev EisensteinLattice := eisensteinLeechModule

theorem eisensteinCoordinateEmbedding_injective : Function.Injective eisensteinCoordinateEmbedding := by
  intro x y h
  funext i
  exact eisensteinToRational_injective (congrFun h i)

def eisensteinIntegralEmbeddingEquiv : EisensteinLattice ≃ₗ[ℤ] rationalEisensteinLattice :=
  Submodule.equivMapOfInjective eisensteinCoordinateEmbedding
    eisensteinCoordinateEmbedding_injective (eisensteinLeechModule.restrictScalars ℤ)

def eisensteinRationalLatticeEquiv : rationalEisensteinLattice ≃ₗ[ℤ] rationalLeech where
  toFun z := ⟨eisensteinComparison z.val, eisensteinComparison_forward z.val z.property⟩
  invFun x := ⟨eisensteinComparison.symm x.val, eisensteinComparison_reverse x.val x.property⟩
  left_inv z := Subtype.ext (eisensteinComparison.symm_apply_apply z.val)
  right_inv x := Subtype.ext (eisensteinComparison.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add eisensteinComparison x.val y.val)
  map_smul' r z := Subtype.ext (map_zsmul eisensteinComparison r z.val)

/-- The integral comparison of the two actual lattices. -/
def eisensteinLeechEquiv : EisensteinLattice ≃ₗ[ℤ] leech :=
  eisensteinIntegralEmbeddingEquiv.trans (eisensteinRationalLatticeEquiv.trans latticeEmbeddingEquiv.symm)

theorem eisensteinLeechEquiv_agrees (z : EisensteinLattice) :
    rationalEmbedding (eisensteinLeechEquiv z).val =
      eisensteinComparison (eisensteinCoordinateEmbedding z.val) := by
  have h := latticeEmbeddingEquiv.apply_symm_apply (eisensteinRationalLatticeEquiv
    (eisensteinIntegralEmbeddingEquiv z))
  exact congrArg Subtype.val h

def eisensteinNorm (z : EisensteinLattice) : ℚ :=
  eisensteinBilinear (eisensteinCoordinateEmbedding z.val) (eisensteinCoordinateEmbedding z.val)

theorem eisensteinNorm_leech (z : EisensteinLattice) :
    eisensteinNorm z = rationalForm (rationalEmbedding (eisensteinLeechEquiv z).val)
      (rationalEmbedding (eisensteinLeechEquiv z).val) := by
  rw [eisensteinLeechEquiv_agrees, eisensteinComparison_isometry]
  rfl

theorem eisensteinNorm_minimum (z : EisensteinLattice) (hz : z ≠ 0) : 4 ≤ eisensteinNorm z := by
  rw [eisensteinNorm_leech]
  apply leech_minimum
  exact fun h => hz (eisensteinLeechEquiv.injective (h.trans (map_zero eisensteinLeechEquiv).symm))

def EisensteinShell (r : ℤ) := {z : EisensteinLattice // eisensteinNorm z = r}

theorem eisensteinNorm_shell_iff (z : EisensteinLattice) (r : ℤ) :
    eisensteinNorm z = r ↔ integerDot (eisensteinLeechEquiv z).val
      (eisensteinLeechEquiv z).val = 8*r := by
  rw [eisensteinNorm_leech, rationalForm_integer]
  constructor
  · intro h
    have he : (integerDot (eisensteinLeechEquiv z).val (eisensteinLeechEquiv z).val : ℚ) =
        ((8*r : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast he
  · intro h
    rw [h]
    push_cast
    ring

def eisensteinShellEquiv (r : ℤ) : EisensteinShell r ≃ LeechShell r :=
  eisensteinLeechEquiv.toEquiv.subtypeEquiv (fun z => eisensteinNorm_shell_iff z r)

theorem eisensteinShell_four_card : Nat.card (EisensteinShell 4) = 196560 := by
  rw [Nat.card_congr (eisensteinShellEquiv 4)]
  exact leech_minimal_shell_card

theorem eisensteinShell_six_card : Nat.card (EisensteinShell 6) = 16773120 := by
  rw [Nat.card_congr (eisensteinShellEquiv 6)]
  exact leech_six_shell_card

end Atlas.Lattices

import Atlas.LinearGroups.ReeF4.WeylSL2Membership
import Atlas.LinearGroups.ReeF4.WeylModel
import Atlas.LinearGroups.ReeF4.SpecialVectors

/-! First explicit leading-coordinate reduction in the retained 26-space.
A4 is the unique highest absolute-grade coordinate and C4 is the next one.
The raw coefficient identities apply to arbitrary vectors: isotropy and the
special-point equation are not assumed. No transitivity or count is asserted.
The Weyl operator is sigma, in agreement with the actual source section-5
SL2 convention (the names are interchanged in section-6 prose). -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert

section Ring
variable {F : Type*} [CommRing F] [CharP F 2]

/-- The long-root shear followed by the actual A4/C4 swap. -/
def highestPivotRaw (u z : F) : TraceZero F ≃ₗ[F] TraceZero F :=
  weylSigma * longSL2Equiv u z

/-- The coefficient to be killed is the old C4 coefficient plus u times A4. -/
theorem highestPivotRaw_top (u z : F) (w : TraceZero F) :
    (highestPivotRaw u z w).val.2 0 7 = w.val.2 2 7 + u*w.val.2 0 7 := rfl

/-- The next coefficient is exactly the old A4 coefficient. -/
theorem highestPivotRaw_next (u z : F) (w : TraceZero F) :
    (highestPivotRaw u z w).val.2 2 7 = w.val.2 0 7 := rfl
end Ring

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Parameter chosen by the nonzero top coefficient; the definition is total,
while its elimination theorem explicitly requires that coefficient nonzero. -/
def highestPivotParameter (w : TraceZero F) : F := w.val.2 2 7 / w.val.2 0 7

def highestPivot (m : ℕ) (w : TraceZero F) : TraceZero F ≃ₗ[F] TraceZero F :=
  highestPivotRaw (highestPivotParameter w) (theta F m (highestPivotParameter w))

theorem highestPivot_top_eq_zero (m : ℕ) (w : TraceZero F)
    (ha : w.val.2 0 7 ≠ 0) : (highestPivot m w w).val.2 0 7 = 0 := by
  change w.val.2 2 7 + (w.val.2 2 7 / w.val.2 0 7)*w.val.2 0 7 = 0
  rw [div_mul_cancel₀ _ ha, CharTwo.add_self_eq_zero]

theorem highestPivot_next (m : ℕ) (w : TraceZero F) :
    (highestPivot m w w).val.2 2 7 = w.val.2 0 7 := rfl

theorem highestPivot_next_ne_zero (m : ℕ) (w : TraceZero F)
    (ha : w.val.2 0 7 ≠ 0) : (highestPivot m w w).val.2 2 7 ≠ 0 := by
  rw [highestPivot_next]
  exact ha

theorem highestPivot_mem_modelSubgroup {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (w : TraceZero F) :
    highestPivot m w ∈ modelSubgroup F m := by
  exact (modelSubgroup F m).mul_mem
    (weylOperator_mem_modelSubgroup m 1)
    (longSL2Parameter_mem_modelSubgroup hcard (highestPivotParameter w))

/-- The explicit pivot as an element of the intrinsic group. -/
def highestPivotModel {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (w : TraceZero F) : Model F m :=
  ⟨highestPivot m w, highestPivot_mem_modelSubgroup hcard w⟩

theorem highestPivot_isSpecial {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (w : TraceZero F) (hw : IsSpecialVector m w) :
    IsSpecialVector m (highestPivot m w w) :=
  hw.map_model (highestPivotModel hcard w)

/-- One actual reduction case, with its unchanged nonzero next coefficient.
This is not yet a theorem about all special vectors or the displayed-generator
subgroup E; its explicit operator word supplies the later E-membership proof. -/
theorem specialVector_highest_pivot {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (w : TraceZero F)
    (hw : IsSpecialVector m w) (ha : w.val.2 0 7 ≠ 0) :
    ∃ g : Model F m, IsSpecialVector m (g.val w) ∧
      (g.val w).val.2 0 7 = 0 ∧
      (g.val w).val.2 2 7 = w.val.2 0 7 ∧ (g.val w).val.2 2 7 ≠ 0 := by
  exact ⟨highestPivotModel hcard w, highestPivot_isSpecial hcard w hw,
    highestPivot_top_eq_zero m w ha, highestPivot_next m w,
    highestPivot_next_ne_zero m w ha⟩

end Atlas.ReeF4

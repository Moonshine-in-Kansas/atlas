import Atlas.LinearGroups.F4.ParabolicTorus
import Atlas.LinearGroups.F4.ShortWeylRootSupport

/-! The fifteen short-root groups fixing the actual marked C₀ vector.
This is one inclusion in the local structure, not a full-stabilizer theorem. -/
noncomputable section
namespace Atlas.F4

def shortRootGrade (r : Fin 24) : ℤ :=
  Weights.slotWeight (2-(shortRootPosition r).1) (shortRootPosition r).2 0

def IsParabolicShort (r : Fin 24) : Prop := 0≤shortRootGrade r
instance (r : Fin 24) : Decidable (IsParabolicShort r) :=
  inferInstanceAs (Decidable (0≤shortRootGrade r))

theorem parabolic_short_count : Fintype.card {r : Fin 24 // IsParabolicShort r}=15 := by
  decide +kernel

theorem radical_short_count : Fintype.card {r : Fin 24 // 0<shortRootGrade r}=9 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Sparse integral columns prove the stabilizer inclusion without field enumeration. -/
theorem parabolic_short_columns : ∀ r : Fin 24, IsParabolicShort r →
    shortRootLinearColumn r 19=0 ∧ shortRootQuadraticColumn r 19=0 := by
  decide +kernel

variable {F : Type*} [Field F]

theorem parabolic_short_coefficients (r : Fin 24) (hr : IsParabolicShort r) :
    shortRootL r (parabolicVector (F:=F))=0 ∧
    shortRootQ r (parabolicVector (F:=F))=0 := by
  have hL : shortRootL r (Atlas.Albert.basisVector (albertCoordinateOfFin 19) :
      Atlas.Albert.Carrier ℤ)=0 := by
    rw [shortRootL_integral_column]; exact (parabolic_short_columns r hr).1
  have hQ : shortRootQ r (Atlas.Albert.basisVector (albertCoordinateOfFin 19) :
      Atlas.Albert.Carrier ℤ)=0 := by
    rw [shortRootQ_integral_column]; exact (parabolic_short_columns r hr).2
  have hL' := congrArg (Atlas.Albert.map (Int.castRingHom F)) hL
  have hQ' := congrArg (Atlas.Albert.map (Int.castRingHom F)) hQ
  rw [←shortRootL_map,Atlas.Albert.map_basisVector] at hL'
  rw [←shortRootQ_map,Atlas.Albert.map_basisVector] at hQ'
  have hz : Atlas.Albert.map (Int.castRingHom F) (0 : Atlas.Albert.Carrier ℤ)=0 := by
    apply Prod.ext
    · ext i; exact map_zero _
    · ext i j; exact map_zero _
  rw [hz] at hL' hQ'
  rw [parabolicVector_eq_basis]
  exact ⟨hL',hQ'⟩

theorem shortRoot_parabolicVector (r : Fin 24) (hr : IsParabolicShort r) (t : F) :
    (shortRoot (shortRootPosition r).1 (shortRootPosition r).2 t).val
      parabolicVector=parabolicVector := by
  rw [shortRoot_polynomial_all,(parabolic_short_coefficients r hr).1,
    (parabolic_short_coefficients r hr).2]
  simp

theorem shortRoot_mem_parabolicPointStabilizer (r : Fin 24)
    (hr : IsParabolicShort r) (t : F) :
    shortRoot (shortRootPosition r).1 (shortRootPosition r).2 t∈parabolicPointStabilizer := by
  apply (mem_parabolicPointStabilizer_iff _).mpr
  exact ⟨1,by simpa using shortRoot_parabolicVector r hr t⟩

end Atlas.F4

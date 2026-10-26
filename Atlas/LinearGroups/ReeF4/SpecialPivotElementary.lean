import Atlas.LinearGroups.ReeF4.SpecialLeadingReductionFramework
import Atlas.LinearGroups.ReeF4.SpecialNegativeA2Pivot
import Atlas.LinearGroups.ReeF4.SpecialFifthPivot
import Atlas.LinearGroups.ReeF4.SpecialThirdPivot
import Atlas.LinearGroups.ReeF4.SpecialSecondPivotDescent
import Atlas.LinearGroups.ReeF4.SpecialPointPivot

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem secondPivot_mem_elementary {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F) : secondPivot hcard u∈elementarySubgroup hcard := by
  exact shortRoot_mem_elementary hcard (secondPivotA u) (secondPivotB m u)

theorem thirdPivot_mem_elementary {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F) : thirdPivot hcard u∈elementarySubgroup hcard := by
  exact longRoot_mem_elementary hcard (thirdPivotParameter m u)

theorem fifthPivot_mem_elementary {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F) : fifthPivot hcard u∈elementarySubgroup hcard := by
  exact shortRoot_mem_elementary hcard (fifthPivotA m u) (fifthPivotB u)

theorem negativeA2Pivot_mem_elementary {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F) : negativeA2Pivot hcard u∈elementarySubgroup hcard := by
  exact longRoot_mem_elementary hcard (negativeA2PivotParameter m u)

theorem negativeC3Pivot_mem_elementary {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F) : negativeC3Pivot hcard u∈elementarySubgroup hcard := by
  exact shortRoot_mem_elementary hcard (negativeC3PivotA u) (negativeC3PivotB m u)

theorem secondPivotDescent_mem_elementary {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F) : secondPivotDescent hcard u∈elementarySubgroup hcard := by
  exact (elementarySubgroup hcard).mul_mem (weylRho_mem_elementary hcard)
    (secondPivot_mem_elementary hcard u)

theorem thirdPivotDescent_mem_elementary {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F) : thirdPivotDescent hcard u∈elementarySubgroup hcard := by
  exact (elementarySubgroup hcard).mul_mem (weylSigma_mem_elementary hcard)
    (thirdPivot_mem_elementary hcard u)

theorem fifthPivotDescent_mem_elementary {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F) : fifthPivotDescent hcard u∈elementarySubgroup hcard := by
  exact (elementarySubgroup hcard).mul_mem (weylRho_mem_elementary hcard)
    (fifthPivot_mem_elementary hcard u)

theorem negativeA2PivotDescent_mem_elementary {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F) : negativeA2PivotDescent hcard u∈elementarySubgroup hcard := by
  exact (elementarySubgroup hcard).mul_mem (weylSigma_mem_elementary hcard)
    (negativeA2Pivot_mem_elementary hcard u)

theorem negativeC3PivotDescent_mem_elementary {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F) : negativeC3PivotDescent hcard u∈elementarySubgroup hcard := by
  exact (elementarySubgroup hcard).mul_mem (weylRho_mem_elementary hcard)
    (negativeC3Pivot_mem_elementary hcard u)

theorem highestPivotModel_mem_elementary {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F) : highestPivotModel hcard u∈elementarySubgroup hcard := by
  have he : highestPivotModel hcard u =
      (⟨weylSigma, weylOperator_mem_modelSubgroup m 1⟩ : Model F m) *
        modelLongSL2RootHom hcard (Multiplicative.ofAdd (highestPivotParameter u)) := by
    apply Subtype.ext
    rfl
  rw [he]
  exact (elementarySubgroup hcard).mul_mem (weylSigma_mem_elementary hcard)
    (longRoot_mem_elementary hcard (highestPivotParameter u))

theorem terminalPivot_mem_elementary {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (a c : F) : terminalPivot hcard a c∈elementarySubgroup hcard := by
  have he : terminalPivot hcard a c =
      (⟨weylSigma, weylOperator_mem_modelSubgroup m 1⟩ : Model F m) *
        modelLongSL2RootHom hcard (Multiplicative.ofAdd (a/c)) := by
    apply Subtype.ext
    rfl
  rw [he]
  exact (elementarySubgroup hcard).mul_mem (weylSigma_mem_elementary hcard)
    (longRoot_mem_elementary hcard (a/c))

theorem terminalScalarNormalizer_mem_elementary {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (c : F) (hc : c≠0) : terminalScalarNormalizer hcard c hc∈elementarySubgroup hcard := by
  exact torus_mem_elementary hcard (Units.mk0 c hc)⁻¹ 1
end Atlas.ReeF4

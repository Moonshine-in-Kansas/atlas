import Atlas.LinearGroups.ReeF4.WeylDihedral
import Atlas.LinearGroups.ReeF4.WeylMembership

/-! The sixteen actual Weyl operators inside the full candidate stabilizer. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

private def weylCandidateRepresentation (σ : F →+* F) :
    candidatePartialStabilizer σ →* (TraceZero F ≃ₗ[F] TraceZero F) :=
  (traceZeroPolynomialStabilizer (F := F)).subtype.comp (candidatePartialStabilizer σ).subtype

private theorem weylCandidateRepresentation_injective (σ : F →+* F) :
    Function.Injective (weylCandidateRepresentation σ) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact h

def weylCandidateElement (σ : F →+* F) (g : Fin 2) : candidatePartialStabilizer σ :=
  ⟨⟨weylOperator g, weylOperator_mem_polynomialStabilizer g⟩,
    weyl_mem_candidatePartialStabilizer σ g⟩

def weylCandidateLift (σ : F →+* F) : DihedralGroup 8 → candidatePartialStabilizer σ
  | .r i => (weylCandidateElement σ 0 * weylCandidateElement σ 1)^i.val
  | .sr i => weylCandidateElement σ 0 *
      (weylCandidateElement σ 0 * weylCandidateElement σ 1)^i.val

private theorem weylCandidateLift_representation (σ : F →+* F) (d : DihedralGroup 8) :
    weylCandidateRepresentation σ (weylCandidateLift σ d) = weylDihedralMap d := by
  cases d <;>
    simp [weylCandidateLift, weylDihedralMap, weylDihedralLift,
      weylCandidateRepresentation, weylCandidateElement, weylOperator] <;> rfl

def weylCandidateMap (σ : F →+* F) : DihedralGroup 8 →* candidatePartialStabilizer σ where
  toFun := weylCandidateLift σ
  map_one' := by
    apply weylCandidateRepresentation_injective σ
    rw [weylCandidateLift_representation, map_one, map_one]
  map_mul' a b := by
    apply weylCandidateRepresentation_injective σ
    rw [map_mul, weylCandidateLift_representation, weylCandidateLift_representation,
      weylCandidateLift_representation, map_mul]

variable [Nontrivial F]

theorem weylCandidateMap_injective (σ : F →+* F) :
    Function.Injective (weylCandidateMap σ) := by
  intro d e h
  apply weylDihedralMap_injective (F := F)
  have hh := congrArg (weylCandidateRepresentation σ) h
  change weylCandidateRepresentation σ (weylCandidateLift σ d) =
    weylCandidateRepresentation σ (weylCandidateLift σ e) at hh
  simpa only [weylCandidateLift_representation] using hh

def candidateWeylSubgroup (σ : F →+* F) : Subgroup (candidatePartialStabilizer σ) :=
  (weylCandidateMap σ).range

def candidateWeylDihedralEquiv (σ : F →+* F) :
    DihedralGroup 8 ≃* candidateWeylSubgroup σ :=
  MonoidHom.ofInjective (weylCandidateMap_injective σ)

theorem card_candidateWeylSubgroup (σ : F →+* F) :
    Nat.card (candidateWeylSubgroup σ) = 16 := by
  rw [← Nat.card_congr (candidateWeylDihedralEquiv σ).toEquiv, DihedralGroup.nat_card]

end Atlas.ReeF4

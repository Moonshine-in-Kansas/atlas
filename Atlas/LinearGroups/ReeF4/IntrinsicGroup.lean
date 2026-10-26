import Atlas.LinearGroups.ReeF4.FullKernelStabilizer
import Atlas.LinearGroups.ReeF4.Twist

/-! The full intrinsic group is literally a subgroup of the linear automorphisms
of the existing trace-zero Albert space. Its defining condition is preservation
of Q/C as polynomials and of the product on the actual admissible pairs. No
order, simplicity, generation or recognition assertion enters this definition. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

def modelSubgroup (m : ℕ) : Subgroup (TraceZero F ≃ₗ[F] TraceZero F) :=
  (candidatePartialStabilizer (thetaInv F m).toRingHom).map
    (traceZeroPolynomialStabilizer (F := F)).subtype

abbrev Model (m : ℕ) : Type _ := ↥(modelSubgroup F m)

variable {F}
theorem mem_modelSubgroup_iff (m : ℕ) (g : TraceZero F ≃ₗ[F] TraceZero F) :
    g ∈ modelSubgroup F m ↔ ∃ h : g ∈ traceZeroPolynomialStabilizer (F := F),
      PreservesCandidatePartial (thetaInv F m).toRingHom ⟨g,h⟩ := by
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact ⟨k.property,hk⟩
  · rintro ⟨h,hg⟩
    exact ⟨⟨g,h⟩,hg,rfl⟩

def modelCandidateEquiv (m : ℕ) :
    Model F m ≃* candidatePartialStabilizer (thetaInv F m).toRingHom :=
  ((candidatePartialStabilizer (thetaInv F m).toRingHom).equivMapOfInjective
    (traceZeroPolynomialStabilizer (F := F)).subtype Subtype.val_injective).symm

def modelLinearEmbedding (m : ℕ) : Model F m →* (TraceZero F ≃ₗ[F] TraceZero F) :=
  (modelSubgroup F m).subtype

theorem modelLinearEmbedding_injective (m : ℕ) :
    Function.Injective (modelLinearEmbedding (F := F) m) := Subtype.val_injective

def modelAlbertEmbedding (m : ℕ) : Model F m →* polynomialStabilizer (F := F) :=
  (candidateAlbertEmbedding (thetaInv F m).toRingHom).comp
    (modelCandidateEquiv m).toMonoidHom

theorem modelAlbertEmbedding_injective (m : ℕ) :
    Function.Injective (modelAlbertEmbedding (F := F) m) :=
  (candidateAlbertEmbedding_injective _).comp (modelCandidateEquiv m).injective

theorem mem_modelSubgroup_iff_kernel (m : ℕ) (g : TraceZero F ≃ₗ[F] TraceZero F) :
    g ∈ modelSubgroup F m ↔ ∃ h : g ∈ traceZeroPolynomialStabilizer (F := F),
      PreservesCandidateKernel (thetaInv F m).toRingHom ⟨g,h⟩ := by
  rw [mem_modelSubgroup_iff]
  exact exists_congr (fun h => preservesCandidatePartial_iff_kernel _ ⟨g,h⟩)

end Atlas.ReeF4

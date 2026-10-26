import Atlas.LinearGroups.ReeF4.ExteriorSpanning
import Atlas.LinearGroups.ReeF4.OppositeValues

/-! A complete candidate extension table, awaiting the generator-preservation gate.
The extra diagonal value is motivated by long-root equivariance, not inferred
from the insufficient printed root tables. No Ree model is defined here. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

/-- This specifies every coefficient, including the extra diagonal direction. -/
def extensionCoefficient : TraceZeroCoordinate → TraceZeroCoordinate → TraceZero F
  | .inl i, .inl j => if i = j then 0 else diagonalVector 1
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0
  | .inr r, .inr s =>
      if s = (r.1, Fin.rev r.2) then oppositeLabelValue r
      else if rootDot (scaledShortRoot r) (scaledShortRoot s) = 0 then
        rootVector (starRootTarget r s)
      else 0

def exteriorLabel (s : ExteriorIndex) (k : Fin 2) : TraceZeroCoordinate :=
  (Fintype.equivFin TraceZeroCoordinate).symm (Set.powersetCard.ofFinEmbEquiv.symm s k)

def proposedStarLinear : (⋀[F]^2 (TraceZero F)) →ₗ[F] TraceZero F :=
  markedExteriorBasis.constr F (fun s => extensionCoefficient (exteriorLabel s 0) (exteriorLabel s 1))

@[simp] theorem proposedStarLinear_basis (s : ExteriorIndex) :
    proposedStarLinear (markedExteriorBasis (F := F) s) =
      extensionCoefficient (exteriorLabel s 0) (exteriorLabel s 1) := by
  simp [proposedStarLinear]

/-- Coefficientwise ring maps on the actual trace kernel. -/
def traceZeroSemilinear (σ : F →+* F) : TraceZero F →ₛₗ[σ] TraceZero F where
  toFun := traceZeroMap σ
  map_add' u v := by
    apply Subtype.ext
    exact Atlas.Albert.map_add σ u.val v.val
  map_smul' a u := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact σ.map_mul _ _
    · funext i j
      exact σ.map_mul _ _

def proposedStarSemilinear (σ : F →+* F) :
    StarCarrier (F := F) →ₛₗ[σ] TraceZero F :=
  (traceZeroSemilinear σ).comp (proposedStarLinear.comp (StarCarrier (F := F)).subtype)

@[simp] theorem proposedStarSemilinear_add (σ : F →+* F)
    (x y : StarCarrier (F := F)) :
    proposedStarSemilinear σ (x+y) = proposedStarSemilinear σ x + proposedStarSemilinear σ y :=
  (proposedStarSemilinear σ).map_add x y

@[simp] theorem proposedStarSemilinear_smul (σ : F →+* F) (a : F)
    (x : StarCarrier (F := F)) :
    proposedStarSemilinear σ (a • x) = σ a • proposedStarSemilinear σ x :=
  (proposedStarSemilinear σ).map_smulₛₗ a x

end Atlas.ReeF4

import Atlas.LinearGroups.Orthogonal.Minus.RankThreeCoordinates
import Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge

/-! The concrete six-dimensional Hodge fixed form is the actual minus norm-tail model. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def tripleCoordinates : ((Fin 2 → K) × K) ≃ₗ[F] (Fin 3 → K) where
  toFun w := ![w.1 0,w.1 1,w.2]
  invFun w := (![w 0,w 1],w 2)
  left_inv w := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl
  right_inv w := by funext i; fin_cases i <;> rfl
  map_add' v w := by funext i; fin_cases i <;> rfl
  map_smul' c w := by funext i; fin_cases i <;> rfl

def rankThreeNormIsometry (hdeg : Module.finrank F K = 2) :
    (form hdeg 2).IsometryEquiv (normTripleForm hdeg) where
  __ := (rankThreeNormCoordinates hdeg).trans (tripleCoordinates (F := F))
  map_app' v := by
    change normTripleForm hdeg (tripleCoordinates (F := F) (rankThreeNormCoordinates hdeg v)) = _
    rw [normTripleForm_apply]
    exact rankThreeNormCoordinates_form hdeg v

/-- An actual F-linear quadratic isometry, with no division by two. -/
def rankThreeHodgeIsometry (hdeg : Module.finrank F K = 2) :
    (form hdeg 2).IsometryEquiv (hodgeFixedForm hdeg) :=
  (rankThreeNormIsometry hdeg).trans (hodgeCoordinatesIsometry hdeg)

end Atlas.Orthogonal.Minus

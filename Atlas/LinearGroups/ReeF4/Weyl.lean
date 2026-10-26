import Atlas.LinearGroups.ReeF4.WeylCoordinates

/-! The two source Weyl permutations on the existing trace-zero Albert module.
The relation proofs are identities of these concrete actions, with no group
recognition or assumed Ree order. -/
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F]

def weylTraceRestriction (e : WilsonCoordinates F ≃ₗ[F] WilsonCoordinates F)
    (he : ∀ w, wilsonTrace (e w) = wilsonTrace w) :
    (wilsonTraceLinear (F := F)).ker ≃ₗ[F] (wilsonTraceLinear (F := F)).ker where
  toFun w := ⟨e w, by change wilsonTrace (e w) = 0; rw [he]; exact w.property⟩
  invFun w := ⟨e.symm w, by
    change wilsonTrace (e.symm w) = 0
    rw [← he (e.symm w), e.apply_symm_apply]
    exact w.property⟩
  left_inv w := by apply Subtype.ext; exact e.symm_apply_apply w
  right_inv w := by apply Subtype.ext; exact e.apply_symm_apply w
  map_add' u v := by apply Subtype.ext; exact e.map_add u v
  map_smul' a w := by apply Subtype.ext; exact e.map_smul a w

def weylRho : TraceZero F ≃ₗ[F] TraceZero F :=
  wilsonTraceZeroEquiv.trans
    ((weylTraceRestriction weylRhoWilson weylRhoCoordinates_trace).trans
      wilsonTraceZeroEquiv.symm)

def weylSigma : TraceZero F ≃ₗ[F] TraceZero F :=
  wilsonTraceZeroEquiv.trans
    ((weylTraceRestriction weylSigmaWilson weylSigmaCoordinates_trace).trans
      wilsonTraceZeroEquiv.symm)

@[simp] theorem weylRho_coordinates (w : TraceZero F) :
    wilsonCoordinatesEquiv (weylRho w : Carrier F) =
      weylRhoCoordinates (wilsonCoordinatesEquiv (w : Carrier F)) := by
  exact wilsonCoordinatesEquiv.apply_symm_apply _

@[simp] theorem weylSigma_coordinates (w : TraceZero F) :
    wilsonCoordinatesEquiv (weylSigma w : Carrier F) =
      weylSigmaCoordinates (wilsonCoordinatesEquiv (w : Carrier F)) := by
  exact wilsonCoordinatesEquiv.apply_symm_apply _

@[simp] theorem weylRho_square : (weylRho (F := F)) ^ 2 = 1 := by
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  apply (wilsonCoordinatesEquiv (F := F)).injective
  change wilsonCoordinatesEquiv (weylRho (weylRho w) : Carrier F) =
    wilsonCoordinatesEquiv (w : Carrier F)
  simp only [weylRho_coordinates, weylRhoCoordinates_involutive]

@[simp] theorem weylSigma_square : (weylSigma (F := F)) ^ 2 = 1 := by
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  apply (wilsonCoordinatesEquiv (F := F)).injective
  change wilsonCoordinatesEquiv (weylSigma (weylSigma w) : Carrier F) =
    wilsonCoordinatesEquiv (w : Carrier F)
  simp only [weylSigma_coordinates, weylSigmaCoordinates_involutive]

set_option maxRecDepth 16384 in
/-- Eight successive products act identically on the trace-zero module. -/
theorem weyl_product_pow_eight : ((weylRho (F := F)) * weylSigma) ^ 8 = 1 := by
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · funext i j
    fin_cases i <;> fin_cases j <;> rfl

end Atlas.ReeF4

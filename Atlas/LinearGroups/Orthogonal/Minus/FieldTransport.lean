import Atlas.LinearGroups.Orthogonal.Minus.Basic
import Atlas.LinearGroups.Orthogonal.ProjectiveFieldTransport

/-! Actual simultaneous base/extension field transport of the norm-plane model. -/
noncomputable section
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
namespace Atlas.Orthogonal.Minus
open Atlas.FiniteQuadratic
variable {F K F' K' : Type*}
  [Field F] [Field K] [Field F'] [Field K']
  [Finite F] [Finite K] [Finite F'] [Finite K'] [Algebra F K] [Algebra F' K']
variable (e : F ≃+* F') (f : K ≃+* K')
  (hc : ∀ a : F, f (algebraMap F K a) = algebraMap F' K' (e a))

include e in
theorem transport_conjugation (x : K) : f (conjugation F K x) = conjugation F' K' (f x) := by
  simp only [conjugation_apply,map_pow]
  rw [Nat.card_congr e.toEquiv]

include hc in
theorem transport_norm (hK : Module.finrank F K = 2) (hK' : Module.finrank F' K' = 2)
    (x : K) : norm F' K' (f x) = e (norm F K x) := by
  apply (algebraMap F' K').injective
  rw [norm_formula hK',← hc,norm_formula hK,map_mul,transport_conjugation e f]

def fieldCoordinates (k : ℕ) : Vector k F K ≃ₛₗ[RingHomClass.toRingHom e] Vector k F' K' where
  toFun x := (fieldCoordinatesD e x.1,f x.2)
  invFun x := ((fieldCoordinatesD e).symm x.1,f.symm x.2)
  left_inv x := Prod.ext ((fieldCoordinatesD e).symm_apply_apply x.1) (f.symm_apply_apply x.2)
  right_inv x := Prod.ext ((fieldCoordinatesD e).apply_symm_apply x.1) (f.apply_symm_apply x.2)
  map_add' x y := Prod.ext (map_add (fieldCoordinatesD e) x.1 y.1) (map_add f x.2 y.2)
  map_smul' a x := by
    apply Prod.ext
    · exact map_smulₛₗ (fieldCoordinatesD e) a x.1
    · change f (a • x.2) = e a • f x.2
      simp only [Algebra.smul_def,map_mul,hc]

theorem fieldCoordinates_form (hK : Module.finrank F K = 2)
    (hK' : Module.finrank F' K' = 2) (k : ℕ) (x : Vector k F K) :
    form hK' k (fieldCoordinates e f hc k x) = e (form hK k x) := by
  change formD k F' (fieldCoordinatesD e x.1) + norm F' K' (f x.2) =
    e (formD k F x.1 + norm F K x.2)
  rw [fieldCoordinatesD_form,transport_norm e f hc hK hK',map_add]

def fieldEquivFull (hK : Module.finrank F K = 2) (hK' : Module.finrank F' K' = 2)
    (k : ℕ) : O hK k ≃* O hK' k :=
  semilinearIsometryGroupTransport e (fieldCoordinates e f hc k) _ _
    (fieldCoordinates_form e f hc hK hK' k)

def fieldEquivElementary (hK : Module.finrank F K = 2) (hK' : Module.finrank F' K' = 2)
    (k : ℕ) : E hK k ≃* E hK' k :=
  semilinearElementaryEquiv e (fieldCoordinates e f hc k) _ _
    (fieldCoordinates_form e f hc hK hK' k)

def fieldEquivProjective (hK : Module.finrank F K = 2) (hK' : Module.finrank F' K' = 2)
    (k : ℕ) : ProjectiveElementary (form hK k) ≃* ProjectiveElementary (form hK' k) :=
  semilinearProjectiveElementaryEquiv e (fieldCoordinates e f hc k) _ _
    (fieldCoordinates_form e f hc hK hK' k)

theorem fieldEquivProjective_projection (hK : Module.finrank F K = 2)
    (hK' : Module.finrank F' K' = 2) (k : ℕ) (g : E hK k) :
    fieldEquivProjective e f hc hK hK' k (projectiveElementaryMap _ g) =
      projectiveElementaryMap _ (fieldEquivElementary e f hc hK hK' k g) := rfl
end Atlas.Orthogonal.Minus

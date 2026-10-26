import Atlas.LinearGroups.Orthogonal.Minus.FieldTransport
import Atlas.LinearGroups.Orthogonal.Minus.IntrinsicEven
import Atlas.LinearGroups.Orthogonal.DicksonValueFieldTransport

/-! Intrinsic kernel transport compatible with full coordinate conjugation and Siegel maps. -/
noncomputable section
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
namespace Atlas.Orthogonal.Minus
open Atlas.Quadratic
variable {F K F' K' : Type*}
  [Field F] [Field K] [Field F'] [Field K']
  [Finite F] [Finite K] [Finite F'] [Finite K'] [Algebra F K] [Algebra F' K']
variable (e : F ≃+* F') (f : K ≃+* K')
  (hc : ∀ a : F, f (algebraMap F K a) = algebraMap F' K' (e a))
variable (hK : Module.finrank F K = 2) (hK' : Module.finrank F' K' = 2)

theorem fieldEquivElementary_full (k : ℕ) (g : E hK k) :
    (fieldEquivElementary e f hc hK hK' k g).val =
      fieldEquivFull e f hc hK hK' k g.val := rfl

def fieldEquivSpinorKernel (n : ℕ) (h2 : (2 : F) ≠ 0) (h2' : (2 : F') ≠ 0) :
    specialSpinorKernel (form hK (n+2)) (polar_nondegenerate hK _) h2 ≃*
      specialSpinorKernel (form hK' (n+2)) (polar_nondegenerate hK' _) h2' :=
  (elementarySpinorEquiv hK n h2).symm |>.trans
    ((fieldEquivElementary e f hc hK hK' (n+2)).trans
      (elementarySpinorEquiv hK' n h2'))

theorem fieldEquivSpinorKernel_full (n : ℕ) (h2 : (2 : F) ≠ 0) (h2' : (2 : F') ≠ 0)
    (g : specialSpinorKernel (form hK (n+2)) (polar_nondegenerate hK _) h2) :
    (fieldEquivSpinorKernel e f hc hK hK' n h2 h2' g).val.val =
      fieldEquivFull e f hc hK hK' (n+2) g.val.val := rfl

/-- The actual residual-rank character commutes with transport before taking its kernel. -/
theorem fullDickson_field_transport (n : ℕ) (g : O hK (n+2)) :
    fullDickson hK' n (fieldEquivFull e f hc hK hK' (n+2) g) = fullDickson hK n g := by
  apply Multiplicative.toAdd.injective
  exact dicksonValue_semilinear_transport e (fieldCoordinates e f hc (n+2))
    _ _ (fieldCoordinates_form e f hc hK hK' (n+2)) g

def fieldEquivDicksonKernel [CharP F 2] [PerfectRing F 2]
    [CharP F' 2] [PerfectRing F' 2] (n : ℕ) :
    (fullDickson hK n).ker ≃* (fullDickson hK' n).ker :=
  (MulEquiv.subgroupCongr (fullDickson_kernel_elementary hK n)).trans
    ((fieldEquivElementary e f hc hK hK' (n+2)).trans
      (MulEquiv.subgroupCongr (fullDickson_kernel_elementary hK' n).symm))

theorem fieldEquivDicksonKernel_full [CharP F 2] [PerfectRing F 2]
    [CharP F' 2] [PerfectRing F' 2] (n : ℕ) (g : (fullDickson hK n).ker) :
    (fieldEquivDicksonKernel e f hc hK hK' n g).val =
      fieldEquivFull e f hc hK hK' (n+2) g.val := rfl

theorem fieldCoordinates_siegel (k : ℕ) (u v x : Vector k F K) :
    fieldCoordinates e f hc k (siegel (form hK k) u v x) =
      siegel (form hK' k) (fieldCoordinates e f hc k u)
        (fieldCoordinates e f hc k v) (fieldCoordinates e f hc k x) :=
  semilinear_siegel_covariant e (fieldCoordinates e f hc k) _ _
    (fieldCoordinates_form e f hc hK hK' k) u v x

theorem fieldEquivFull_siegelElement (k : ℕ) (u v : Vector k F K)
    (hu : form hK k u = 0) (huv : (form hK k).polarBilin u v = 0) :
    fieldEquivFull e f hc hK hK' k (siegelElement (form hK k) u v hu huv) =
      siegelElement (form hK' k) (fieldCoordinates e f hc k u)
        (fieldCoordinates e f hc k v)
        (by rw [fieldCoordinates_form e f hc hK hK' k, hu, map_zero])
        (by rw [semilinear_polar_transport e (fieldCoordinates e f hc k) _ _
          (fieldCoordinates_form e f hc hK hK' k), huv, map_zero]) :=
  semilinear_siegelElement e (fieldCoordinates e f hc k) _ _
    (fieldCoordinates_form e f hc hK hK' k) u v hu huv
end Atlas.Orthogonal.Minus

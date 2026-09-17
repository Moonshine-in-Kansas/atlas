import Atlas.Fischer.RationalCocodeAction
import Atlas.Fischer.RealProduct
import Atlas.Fischer.ParkerMultiplicativity

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def GolayCommonEigenvector (c : golay) (x : Coordinates) : Prop :=
  ∀ d : Cocode, parkerCoordinateAction (parkerCocodeStandard d) x=
    rationalBitSign (cocodePairing c d) • x

theorem rationalBitSign_smul_scalar (b : Bit) (x : Coordinates) :
    rationalBitSign b • x=parkerScalarSign b • x := by
  by_cases hb : b=0 <;> simp [rationalBitSign,parkerScalarSign,hb]

theorem cocodePairing_separates (a b : golay)
    (h : ∀ d, cocodePairing a d=cocodePairing b d) : a=b := by
  apply Subtype.ext
  funext i
  let l : Module.Dual Bit golay := (LinearMap.proj i).comp golay.subtype
  obtain ⟨d,hd⟩ := cocodeDualEquiv.surjective l
  have he := h d
  change cocodeDualEquiv d a=cocodeDualEquiv d b at he
  rw [hd] at he
  exact he

/-- The full actual cocode gives the exact Golay label of every nonzero
rational coordinate, including the θ directions and all point coordinates. -/
theorem golayCommonEigenvector_iff (c : golay) (x : Coordinates) :
    GolayCommonEigenvector c x ↔
      ∀ p : RationalCoordinateIndex, rationalCoordinateGolayWord p ≠ c → rationalCoordinateEquiv x p=0 := by
  constructor
  · intro hx p hp
    by_contra hn
    apply hp
    apply cocodePairing_separates
    intro d
    have he := congrArg (fun y => rationalCoordinateEquiv y p) (hx d)
    rw [rationalCoordinateEquiv_cocode,map_smul,Pi.smul_apply] at he
    exact rationalBitSign_injective (mul_right_cancel₀ hn he)
  · intro hx d
    apply rationalCoordinateEquiv.injective
    funext p
    rw [rationalCoordinateEquiv_cocode,map_smul,Pi.smul_apply]
    by_cases hp : rationalCoordinateGolayWord p=c
    · rw [hp]
      rfl
    · rw [hx p hp,mul_zero,smul_zero]

theorem golayCommonEigenvector_product (a b : golay) (x y : Coordinates)
    (hx : GolayCommonEigenvector a x) (hy : GolayCommonEigenvector b y) :
    GolayCommonEigenvector (a+b) (product x y) := by
  intro d
  rw [parkerCoordinateAction_product,hx d,hy d,product_rat_smul_left,product_rat_smul_right,smul_smul]
  have ha : cocodePairing (a+b) d=cocodePairing a d+cocodePairing b d := map_add (cocodeDualEquiv d) _ _
  rw [ha]
  have hs : ∀ u v : Bit, rationalBitSign (u+v)=rationalBitSign u*rationalBitSign v := by
    have hb : ∀ t : Bit, t=0 ∨ t=1 := by decide
    intro u v
    rcases hb u with rfl | rfl <;> rcases hb v with rfl | rfl <;>
      norm_num [rationalBitSign,show (1 : Bit)+1=0 from rfl] <;> decide
  rw [hs]

end Atlas.Fischer

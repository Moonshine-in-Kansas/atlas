import Atlas.Fischer.RootProductSquare
import Atlas.Fischer.RootPhases

noncomputable section
namespace Atlas.Fischer

/-- An antiunitary normalized root makes multiplication by that root surjective. -/
theorem rootProduct_surjective (r : Coordinates) (hr : IsRoot r)
    (ha : RootMapAntiunitary r) : Function.Surjective (fun x => product x r) := by
  intro x
  refine ⟨product x r - ((11 / 10 : Scalar) * star (hermitian x r)) • r, ?_⟩
  have hsq := congrArg (fun f : Module.End Scalar Coordinates => f x)
    (rootProduct_square r hr.1 hr.2 ha)
  change product (product x r) r=x+(11 : Scalar) • (hermitian x r • r) at hsq
  dsimp only
  rw [product_sub_left,product_smul_left,hsq,hr.2,star_mul,star_star]
  norm_num
  module

/-- The actual centroid condition for an E-linear endomorphism of the
conjugate-bilinear nonassociative product. -/
def IsProductCentroid (S : Module.End Scalar Coordinates) : Prop :=
  ∀ x y, S (product x y)=product (S x) y ∧ S (product x y)=product x (S y)

/-- One antiunitary normalized root forces the E-linear centroid to consist
of conjugation-fixed scalar maps. No irreducibility or moment input is used. -/
theorem productCentroid_scalar (S : Module.End Scalar Coordinates)
    (hS : IsProductCentroid S) (r : Coordinates) (hr : IsRoot r)
    (ha : RootMapAntiunitary r) :
    ∃ a : Scalar, star a=a ∧ ∀ x, S x=a • x := by
  have he : product (S r) r=(10 : Scalar) • S r := by
    rw [← (hS r r).1,hr.2,S.map_smul]
  have hsq := congrArg (fun f : Module.End Scalar Coordinates => f (S r))
    (rootProduct_square r hr.1 hr.2 ha)
  change product (product (S r) r) r=S r+(11 : Scalar) • (hermitian (S r) r • r) at hsq
  rw [he,product_smul_left,he] at hsq
  norm_num at hsq
  let a : Scalar := hermitian (S r) r/9
  have hs : S r=a • r := by
    dsimp [a]
    linear_combination (norm := module) (1 / 99 : Scalar) • hsq
  have he' := he
  rw [hs,product_smul_left,hr.2,smul_smul,smul_smul] at he'
  have hc := smul_left_injective Scalar (root_ne_zero hr) he'
  have har : star a=a := by
    linear_combination hc / 10
  refine ⟨a,har,?_⟩
  intro x
  obtain ⟨y,rfl⟩ := rootProduct_surjective r hr ha x
  rw [(hS y r).2,hs,product_smul_right,har]

end Atlas.Fischer

import Atlas.Fischer.ResiduePerfectness
import Atlas.Fischer.ResidueProductOrders
import Atlas.GroupTheory.PrimitiveMap
import Mathlib.GroupTheory.GroupAction.ConjAct

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Equivariance into the actual quotient with its conjugation action. -/
def residueDistinguishedMap (S : Finset Omega) :
    ResiduePoint S →ₑ[(ConjAct.toConjAct : ResidueGroup S ≃* ConjAct (ResidueGroup S))]
      ResidueGroup S where
  toFun := residueDistinguishedElement S
  map_smul' g x := by
    rw [ConjAct.toConjAct_smul]
    exact (residueDistinguishedElement_covariance S g x).symm

/-- Primitivity and an actual surviving order-three pair give distinct quotient involutions. -/
theorem residueDistinguished_injective_of_primitive (S : Finset Omega)
    [MulAction.IsPreprimitive (ResidueGroup S) (ResiduePoint S)]
    (hw : ∃ x y : ResiduePoint S, orderOf (x.val*y.val)=3) :
    Function.Injective (residueDistinguishedElement S) := by
  rcases Atlas.GroupTheory.primitive_map_injective_or_constant (residueDistinguishedMap S)
    with hi | hc
  · exact hi
  · obtain ⟨x,y,hxy⟩ := hw
    have he : residueDistinguishedElement S x=residueDistinguishedElement S y := hc x y
    have ho := residueDistinguished_product_order_three S x y hxy
    rw [he,← pow_two,residueDistinguishedElement_square,orderOf_one] at ho
    norm_num at ho

/-- Nonidentity is proved separately from the generic simple-group predicate. -/
theorem residueDistinguished_ne_one_of_order_three (S : Finset Omega) (hS : S.card≤2)
    (hw : ∃ x y : ResiduePoint S, orderOf (x.val*y.val)=3) (x : ResiduePoint S) :
    residueDistinguishedElement S x ≠ 1 := by
  intro hx
  obtain ⟨u,v,huv⟩ := hw
  haveI := residueGroup_transitive S (by omega)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ResidueGroup S) x u
  have hu := residueDistinguishedElement_covariance S g x
  rw [hg,hx] at hu
  have hu1 : residueDistinguishedElement S u=1 := by simpa using hu.symm
  have ho := residueDistinguished_product_order_three S u v huv
  rw [hu1,one_mul] at ho
  have hd := orderOf_dvd_of_pow_eq_one (residueDistinguishedElement_square S v)
  rw [ho] at hd
  norm_num at hd

theorem residueDistinguished_order_of_order_three (S : Finset Omega) (hS : S.card≤2)
    (hw : ∃ x y : ResiduePoint S, orderOf (x.val*y.val)=3) (x : ResiduePoint S) :
    orderOf (residueDistinguishedElement S x)=2 :=
  orderOf_eq_prime (residueDistinguishedElement_square S x)
    (residueDistinguished_ne_one_of_order_three S hS hw x)

end Atlas.Fischer

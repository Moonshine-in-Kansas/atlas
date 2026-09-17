import Atlas.Fischer.RootRayPermutationInvertibility

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Transport the actual product by an arbitrary parity-semilinear equivalence. -/
def parityTransportedProduct (b : Bit)
    (g : Coordinates ≃ₛₗ[(scalarParityAut b).toRingHom] Coordinates) :
    Coordinates →ₛₗ[starRingEnd Scalar] Coordinates →ₛₗ[starRingEnd Scalar] Coordinates where
  toFun x :=
    { toFun := fun y => g.symm (product (g x) (g y))
      map_add' := by intro y z; rw [map_add,product_add_right,map_add]
      map_smul' := by
        intro c y
        rw [map_smulₛₗ,product_smul_right,map_smulₛₗ]
        change scalarParityAut b (star (scalarParityAut b c)) • _=star c • _
        rw [scalarParityAut_star,scalarParityAut_involutive] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change g.symm (product (g (x+y)) (g z))=_
    rw [map_add,product_add_left,map_add]
    rfl
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    change g.symm (product (g (c • x)) (g y))=star c • g.symm (product (g x) (g y))
    rw [map_smulₛₗ,product_smul_left,map_smulₛₗ]
    change scalarParityAut b (star (scalarParityAut b c)) • _=star c • _
    rw [scalarParityAut_star,scalarParityAut_involutive]

/-- Quadratic reconstruction forces any invertible semilinear map sending the
full reflecting representatives to roots to preserve multiplication. -/
theorem reflectingRoot_transport_product {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (hc : Fintype.card J=306936) (b : Bit)
    (g : Coordinates ≃ₛₗ[(scalarParityAut b).toRingHom] Coordinates)
    (hg : ∀ j, IsRoot (g (r j))) (x y : Coordinates) :
    g (product x y)=product (g x) (g y) := by
  have h := reflectingRoot_product_unique r hr hd hc (parityTransportedProduct b g)
    (by intro u v; change g.symm (product (g u) (g v))=g.symm (product (g v) (g u)); rw [product_comm])
    (by
      intro j
      change g.symm (product (g (r j)) (g (r j)))=(10 : Scalar) • r j
      rw [(hg j).2,map_smulₛₗ,g.symm_apply_apply]
      change scalarParityAut b (10 : Scalar) • r j = _
      rw [map_ofNat])
    x y
  have he := congrArg g h
  simpa only [parityTransportedProduct,LinearMap.coe_mk,AddHom.coe_mk,g.apply_symm_apply] using he.symm

end Atlas.Fischer

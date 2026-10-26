import Atlas.Algebra.Albert.UniversalCriterion

/-! Functorial coefficient extension of Albert linear automorphisms. -/
noncomputable section
namespace Atlas.Albert
open Matrix
variable {F R S : Type*} [CommRing F] [CommRing R] [CommRing S]

def scalarExtensionEquiv (g : Carrier F ≃ₗ[F] Carrier F) (f : F →+* R) :
    Carrier R ≃ₗ[R] Carrier R :=
  (coordinateEquiv.trans
    ((GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv R (Coordinate → R)))
        (GeneralLinearGroup.map f (matrixRepresentation g)))).trans coordinateEquiv.symm

theorem scalarExtensionEquiv_apply (g : Carrier F ≃ₗ[F] Carrier F)
    (f : F →+* R) (x : Carrier R) :
    scalarExtensionEquiv g f x = scalarExtension g f x := by
  apply coordinateEquiv.injective
  rw [scalarExtension_coordinates]
  simp only [scalarExtensionEquiv,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  rfl

theorem scalarExtensionEquiv_map (g : Carrier F ≃ₗ[F] Carrier F)
    (f : F →+* R) (x : Carrier F) :
    scalarExtensionEquiv g f (map f x) = map f (g x) := by
  rw [scalarExtensionEquiv_apply,scalarExtension_map]

theorem map_comp (f : F →+* R) (h : R →+* S) (x : Carrier F) :
    map h (map f x) = map (h.comp f) x := rfl

theorem scalarExtension_comp (g : Carrier F ≃ₗ[F] Carrier F)
    (f : F →+* R) (h : R →+* S) :
    scalarExtension (scalarExtensionEquiv g f) h = scalarExtension g (h.comp f) := by
  apply linearMap_ext_basis
  intro i
  rw [←map_basisVector h i,scalarExtension_map]
  rw [←map_basisVector f i,scalarExtensionEquiv_map,map_comp]
  rw [map_comp,scalarExtension_map]

def extendLinear (f : F →+* R) : (Carrier F ≃ₗ[F] Carrier F) →*
    (Carrier R ≃ₗ[R] Carrier R) where
  toFun g := scalarExtensionEquiv g f
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    apply linearMap_ext_basis
    intro i
    change scalarExtensionEquiv 1 f (basisVector i) = basisVector i
    rw [←map_basisVector f i,scalarExtensionEquiv_map]
    rfl
  map_mul' g h := by
    apply LinearEquiv.toLinearMap_injective
    apply linearMap_ext_basis
    intro i
    change scalarExtensionEquiv (g*h) f (basisVector i) =
      scalarExtensionEquiv g f (scalarExtensionEquiv h f (basisVector i))
    rw [←map_basisVector f i,scalarExtensionEquiv_map,
      scalarExtensionEquiv_map,scalarExtensionEquiv_map]
    rfl

def extendStabilizer (f : F →+* R) : polynomialStabilizer (F:=F) →*
    polynomialStabilizer (F:=R) where
  toFun g := ofUniversalNorm (extendLinear f g.val)
    (by
      change scalarExtensionEquiv g.val f unit = unit
      rw [scalarExtensionEquiv_apply]
      exact scalarExtension_unit g f)
    (by
      change norm (scalarExtension (scalarExtensionEquiv g.val f) _ _) = _
      rw [scalarExtension_comp,scalarExtension_norm]
      rfl)
  map_one' := Subtype.ext (_root_.map_one (extendLinear f))
  map_mul' g h := Subtype.ext (_root_.map_mul (extendLinear f) g.val h.val)

theorem extendStabilizer_map (f : F →+* R) (g : polynomialStabilizer (F:=F))
    (x : Carrier F) : (extendStabilizer f g).val (map f x) = map f (g.val x) :=
  scalarExtensionEquiv_map g.val f x

end Atlas.Albert

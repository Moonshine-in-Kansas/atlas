import Atlas.LinearGroups.F4.Basic
import Atlas.Algebra.Albert.UniversalCriterion
import Atlas.Algebra.SplitOctonion.ScalarExtension
import Mathlib.RingTheory.Localization.FractionRing

/-! The actual coefficientwise G₂ inclusion into the full Albert cubic stabilizer.
Polynomial preservation is proved after an injective map from the universal
polynomial ring into its fraction field, not by testing values over F. -/
noncomputable section
namespace Atlas.F4
variable {F K : Type*} [Field F] [Field K]

def octonionAction (g : Atlas.SplitOctonion.Automorphism F) :
    Atlas.Albert.Carrier F ≃ₗ[F] Atlas.Albert.Carrier F where
  toFun x := (x.1,fun i=>g.val (x.2 i))
  invFun x := (x.1,fun i=>g.val.symm (x.2 i))
  left_inv x := by apply Prod.ext; rfl; funext i; exact g.val.symm_apply_apply _
  right_inv x := by apply Prod.ext; rfl; funext i; exact g.val.apply_symm_apply _
  map_add' x y := by apply Prod.ext; rfl; funext i; exact map_add g.val (x.2 i) (y.2 i)
  map_smul' r x := by apply Prod.ext; rfl; funext i; exact map_smul g.val r (x.2 i)

theorem octonionAction_unit (g : Atlas.SplitOctonion.Automorphism F) :
    octonionAction g Atlas.Albert.unit=Atlas.Albert.unit := by
  apply Prod.ext
  · rfl
  · funext i
    exact map_zero g.val

theorem octonionAction_norm (g : Atlas.SplitOctonion.Automorphism F) (x : Atlas.Albert.Carrier F) :
    Atlas.Albert.norm (octonionAction g x)=Atlas.Albert.norm x := by
  simp only [octonionAction,LinearEquiv.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,Atlas.Albert.norm,
    Atlas.SplitOctonion.automorphism_norm]
  rw [←Atlas.SplitOctonion.automorphism_mul,←Atlas.SplitOctonion.automorphism_mul,
    Atlas.SplitOctonion.automorphism_trace]

theorem octonionAction_map (φ : F →+* K) (g : Atlas.SplitOctonion.Automorphism F)
    (x : Atlas.Albert.Carrier F) :
    octonionAction (Atlas.SplitOctonion.Extension.extend φ g) (Atlas.Albert.map φ x)=
      Atlas.Albert.map φ (octonionAction g x) := by
  apply Prod.ext
  · rfl
  · funext i
    exact Atlas.SplitOctonion.Extension.extend_coefficients φ g (x.2 i)

theorem octonionAction_scalarExtension (φ : F →+* K) (g : Atlas.SplitOctonion.Automorphism F) :
    Atlas.Albert.scalarExtension (octonionAction g) φ=
      (octonionAction (Atlas.SplitOctonion.Extension.extend φ g)).toLinearMap :=
  Atlas.Albert.scalarExtension_eq _ _ _ (octonionAction_map φ g)

section ChangeCoefficients
variable {R S : Type*} [CommRing R] [CommRing S]

theorem albert_scalarExtension_map (g : Atlas.Albert.Carrier F ≃ₗ[F] Atlas.Albert.Carrier F)
    (φ : F →+* R) (ψ : R →+* S) (x : Atlas.Albert.Carrier R) :
    Atlas.Albert.map ψ (Atlas.Albert.scalarExtension g φ x)=
      Atlas.Albert.scalarExtension g (ψ.comp φ) (Atlas.Albert.map ψ x) := by
  apply Atlas.Albert.coordinateEquiv.injective
  rw [Atlas.Albert.coordinate_map,Atlas.Albert.scalarExtension_coordinates,
    Atlas.Albert.scalarExtension_coordinates,Atlas.Albert.coordinate_map]
  ext i
  exact ψ.map_mulVec ((Atlas.Albert.matrixRepresentation g).val.map φ)
    (Atlas.Albert.coordinateEquiv x) i

end ChangeCoefficients

theorem octonionAction_universal_norm (g : Atlas.SplitOctonion.Automorphism F) :
    Atlas.Albert.norm (Atlas.Albert.scalarExtension (octonionAction g) MvPolynomial.C
      Atlas.Albert.universalVector)=Atlas.Albert.normPolynomial := by
  let P := MvPolynomial Atlas.Albert.Coordinate F
  let L := FractionRing P
  let ψ : P →+* L := algebraMap P L
  apply IsFractionRing.injective P L
  change ψ _=ψ _
  rw [←Atlas.Albert.norm_map,albert_scalarExtension_map,octonionAction_scalarExtension]
  change Atlas.Albert.norm (octonionAction
    (Atlas.SplitOctonion.Extension.extend (ψ.comp MvPolynomial.C) g)
    (Atlas.Albert.map ψ Atlas.Albert.universalVector))=ψ Atlas.Albert.normPolynomial
  rw [octonionAction_norm,Atlas.Albert.norm_map]
  rfl

/-- Coefficientwise octonion automorphisms are genuine polynomial Albert automorphisms. -/
def g2Embedding : Atlas.SplitOctonion.Automorphism F →* Model F where
  toFun g := Atlas.Albert.ofUniversalNorm (octonionAction g)
    (octonionAction_unit g) (octonionAction_universal_norm g)
  map_one' := by apply Subtype.ext; apply LinearEquiv.ext; intro x; rfl
  map_mul' g h := by apply Subtype.ext; apply LinearEquiv.ext; intro x; rfl

theorem g2Embedding_injective : Function.Injective (g2Embedding (F:=F)) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hx := congrArg (fun a : Model F=>(a.val (0,fun _=>x)).2 0) he
  exact hx

end Atlas.F4

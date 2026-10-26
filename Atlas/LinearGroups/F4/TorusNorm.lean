import Atlas.LinearGroups.F4.TorusMaps
import Atlas.LinearGroups.F4.G2Embedding

noncomputable section
namespace Atlas.F4

section Naturality
variable {F R : Type*} [CommRing F] [CommRing R]

def torusParametersMap (φ : F →+* R) (t : TorusParameters F) : TorusParameters R :=
  fun i => Units.map φ.toMonoidHom (t i)

theorem torusScale_map (φ : F →+* R) (t : TorusParameters F) (i : Fin 3) (j : Fin 8) :
    torusScale (torusParametersMap φ t) i j = Units.map φ.toMonoidHom (torusScale t i j) := by
  simp [torusScale, weightCharacter, torusParametersMap, map_prod]

theorem torusEquiv_map (φ : F →+* R) (t : TorusParameters F) (x : Atlas.Albert.Carrier F) :
    torusEquiv (torusParametersMap φ t) (Atlas.Albert.map φ x) =
      Atlas.Albert.map φ (torusEquiv t x) := by
  apply Prod.ext
  · rfl
  · funext i j
    change (torusScale (torusParametersMap φ t) i j : R) * φ (x.2 i j) =
      φ ((torusScale t i j : F) * x.2 i j)
    rw [torusScale_map]
    simp

theorem torusEquiv_scalarExtension (φ : F →+* R) (t : TorusParameters F) :
    Atlas.Albert.scalarExtension (torusEquiv t) φ =
      (torusEquiv (torusParametersMap φ t)).toLinearMap :=
  Atlas.Albert.scalarExtension_eq _ _ _ (torusEquiv_map φ t)

end Naturality

variable {F : Type*} [Field F]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
/-- Direct verification for the sparse Albert cubic; all four unit parameters remain free. -/
theorem torusEquiv_norm (t : TorusParameters F) (x : Atlas.Albert.Carrier F) :
    Atlas.Albert.norm (torusEquiv t x) = Atlas.Albert.norm x := by
  simp [torusEquiv, torusApply, torusScale, weightCharacter, RootData.simpleCoefficients,
    RootData.coordinates, Weights.slotRoot, Fin.prod_univ_succ, Atlas.Albert.norm,
    Atlas.SplitOctonion.norm, Atlas.SplitOctonion.trace, Atlas.SplitOctonion.mul]
  field_simp <;> ring

/-- Polynomial preservation is checked over the universal polynomial ring through
its injective map to the fraction field. Finite-field values alone are not used. -/
theorem torus_universal_norm (t : TorusParameters F) :
    Atlas.Albert.norm (Atlas.Albert.scalarExtension (torusEquiv t) MvPolynomial.C
      Atlas.Albert.universalVector) = Atlas.Albert.normPolynomial := by
  let P := MvPolynomial Atlas.Albert.Coordinate F
  let L := FractionRing P
  let ψ : P →+* L := algebraMap P L
  apply IsFractionRing.injective P L
  change ψ _ = ψ _
  rw [← Atlas.Albert.norm_map, albert_scalarExtension_map, torusEquiv_scalarExtension]
  change Atlas.Albert.norm (torusEquiv (torusParametersMap (ψ.comp MvPolynomial.C) t)
    (Atlas.Albert.map ψ Atlas.Albert.universalVector)) = ψ Atlas.Albert.normPolynomial
  rw [torusEquiv_norm, Atlas.Albert.norm_map]
  rfl

def diagonalTorus : TorusParameters F →* Model F where
  toFun t := Atlas.Albert.ofUniversalNorm (torusEquiv t)
    (torusEquiv_unit t) (torus_universal_norm t)
  map_one' := by apply Subtype.ext; exact torusEquiv_one
  map_mul' s t := by apply Subtype.ext; exact torusEquiv_mul s t

theorem diagonalTorus_injective : Function.Injective (diagonalTorus (F := F)) := by
  intro s t h
  apply diagonalTorusLinear_injective
  exact congrArg Subtype.val h

end Atlas.F4

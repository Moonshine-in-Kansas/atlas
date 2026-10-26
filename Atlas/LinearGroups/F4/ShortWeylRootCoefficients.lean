import Atlas.LinearGroups.F4.ShortWeylRootPolynomial

noncomputable section
namespace Atlas.F4
variable {R : Type*} [CommRing R]

def shortRootPosition (r : Fin 24) : Fin 3 × Fin 8 :=
  (⟨r.val/8,by omega⟩,⟨r.val%8,by omega⟩)

def cycleCoefficient (p : Fin 3) (f : Atlas.Albert.Carrier R →ₗ[R] Atlas.Albert.Carrier R) :
    Atlas.Albert.Carrier R →ₗ[R] Atlas.Albert.Carrier R :=
  (Atlas.Albert.coordinateCycleEquiv ^ p.val).toLinearMap.comp
    (f.comp (Atlas.Albert.coordinateCycleEquiv ^ p.val).symm.toLinearMap)

def shortRootL (r : Fin 24) : Atlas.Albert.Carrier R →ₗ[R] Atlas.Albert.Carrier R :=
  cycleCoefficient (shortRootPosition r).1 (shortRootFirstCoefficient (shortRootPosition r).2)

def shortRootQ (r : Fin 24) : Atlas.Albert.Carrier R →ₗ[R] Atlas.Albert.Carrier R :=
  cycleCoefficient (shortRootPosition r).1
    (shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector (shortRootPosition r).2))

theorem coordinateCyclePow_map {S : Type*} [CommRing S] (φ : R →+* S)
    (n : ℕ) (x : Atlas.Albert.Carrier R) :
    (Atlas.Albert.coordinateCycleEquiv ^ n) (Atlas.Albert.map φ x) =
      Atlas.Albert.map φ ((Atlas.Albert.coordinateCycleEquiv ^ n) x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ, LinearEquiv.mul_apply, Atlas.Albert.coordinateCycleEquiv_apply,
      Atlas.Albert.coordinateCycle_map, ih]

theorem coordinateCyclePow_symm_map {S : Type*} [CommRing S] (φ : R →+* S)
    (n : ℕ) (x : Atlas.Albert.Carrier R) :
    (Atlas.Albert.coordinateCycleEquiv ^ n).symm (Atlas.Albert.map φ x) =
      Atlas.Albert.map φ ((Atlas.Albert.coordinateCycleEquiv ^ n).symm x) := by
  apply (Atlas.Albert.coordinateCycleEquiv ^ n).injective
  rw [LinearEquiv.apply_symm_apply, coordinateCyclePow_map, LinearEquiv.apply_symm_apply]

theorem shortRootL_map {S : Type*} [CommRing S] (φ : R →+* S) (r : Fin 24)
    (x : Atlas.Albert.Carrier R) :
    shortRootL r (Atlas.Albert.map φ x) = Atlas.Albert.map φ (shortRootL r x) := by
  simp only [shortRootL, cycleCoefficient, LinearMap.comp_apply, LinearEquiv.coe_coe,
    coordinateCyclePow_symm_map, shortRootFirstCoefficient_map, coordinateCyclePow_map]

theorem shortRootQ_map {S : Type*} [CommRing S] (φ : R →+* S) (r : Fin 24)
    (x : Atlas.Albert.Carrier R) :
    shortRootQ r (Atlas.Albert.map φ x) = Atlas.Albert.map φ (shortRootQ r x) := by
  simp only [shortRootQ, cycleCoefficient, LinearMap.comp_apply, LinearEquiv.coe_coe,
    coordinateCyclePow_symm_map, shortRootQuadratic_basis_map, coordinateCyclePow_map]

variable {F : Type*} [Field F]

theorem shortRoot_polynomial_all (r : Fin 24) (t : F) (x : Atlas.Albert.Carrier F) :
    (shortRoot (shortRootPosition r).1 (shortRootPosition r).2 t).val x =
      x + t • shortRootL r x + t^2 • shortRootQ r x := by
  change (Atlas.Albert.coordinateCycleEquiv ^ (shortRootPosition r).1.val)
    (Atlas.Albert.shortRootLinear (shortRootPosition r).2 t
      ((Atlas.Albert.coordinateCycleEquiv ^ (shortRootPosition r).1.val).symm x)) = _
  rw [shortRoot_polynomial, map_add, map_add, map_smul, map_smul,
    LinearEquiv.apply_symm_apply]
  rfl

end Atlas.F4

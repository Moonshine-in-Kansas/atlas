import Atlas.LinearGroups.ReeF4.TorusStarCoefficient

/-! The source torus preserves the candidate on the entire exterior square
semilinearly, hence also the prescribed polar/cross kernel and partial product.
No arbitrary-value extension outside the partial domain is used as a definition
of the group: the final membership is in the actual partial stabilizer. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem torusStar_marked {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (a b : Fˣ) (i j : TraceZeroCoordinate) :
    traceZeroScalarMap (thetaInv F m).toRingHom
      (proposedStarLinear (wedge (torusEquiv m a b (markedBasis i))
        (torusEquiv m a b (markedBasis j)))) =
      torusEquiv m a b (traceZeroScalarMap (thetaInv F m).toRingHom
        (proposedStarLinear (wedge (markedBasis i) (markedBasis j)))) := by
  rw [torusEquiv_marked, torusEquiv_marked, wedge_smul_left, wedge_smul_right]
  simp only [map_smul, LinearMap.map_smulₛₗ, proposedStarLinear_marked_wedge,
    traceZeroScalarMap_apply, extensionCoefficient_map]
  rw [smul_smul]
  change ((thetaInv F m) (markedTorusWeight m a b i) *
      (thetaInv F m) (markedTorusWeight m a b j)) • extensionCoefficient i j =
    torusEquiv m a b (extensionCoefficient i j)
  simpa only [map_mul, smul_smul] using torusStarCoefficient hcard a b i j

private theorem exterior_basis_wedge (s : ExteriorIndex) :
    markedExteriorBasis (F := F) s =
      wedge (markedBasis (exteriorLabel s 0)) (markedBasis (exteriorLabel s 1)) := by
  simp only [markedExteriorBasis, exteriorPower.coe_basis, exteriorPower.ιMulti_family,
    orderedMarkedBasis, Module.Basis.reindex_apply, exteriorLabel, wedge]
  congr 1
  funext k
  fin_cases k <;> simp [Function.comp_apply, Module.Basis.reindex_apply]

theorem torusStar_exterior {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (a b : Fˣ) :
    (traceZeroScalarMap (thetaInv F m).toRingHom).comp
      (proposedStarLinear.comp (exteriorPower.map 2 (torusEquiv m a b).toLinearMap)) =
    (torusEquiv m a b).toLinearMap.comp
      ((traceZeroScalarMap (thetaInv F m).toRingHom).comp proposedStarLinear) := by
  apply markedExteriorBasis.ext
  intro s
  simp only [LinearMap.comp_apply, exterior_basis_wedge]
  have hw (u v : TraceZero F) :
      exteriorPower.map 2 (torusEquiv m a b).toLinearMap (wedge u v) =
        wedge (torusEquiv m a b u) (torusEquiv m a b v) := by
    simp only [wedge, exteriorPower.map_apply_ιMulti]
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [hw]
  exact torusStar_marked hcard a b _ _

theorem torus_mem_candidatePartialStabilizer {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b : Fˣ) :
    (⟨torusEquiv m a b, torusEquiv_mem_polynomialStabilizer m a b⟩ :
      traceZeroPolynomialStabilizer (F := F)) ∈
        candidatePartialStabilizer (thetaInv F m).toRingHom := by
  intro u v huv
  have h := LinearMap.congr_fun (torusStar_exterior hcard a b) (wedge u v)
  have hw : exteriorPower.map 2 (torusEquiv m a b).toLinearMap (wedge u v) =
      wedge (torusEquiv m a b u) (torusEquiv m a b v) := by
    simp only [wedge, exteriorPower.map_apply_ιMulti]
    congr 1
    funext k
    fin_cases k <;> rfl
  change traceZeroMap (thetaInv F m).toRingHom
      (proposedStarLinear (wedge (torusEquiv m a b u) (torusEquiv m a b v))) =
    torusEquiv m a b (traceZeroMap (thetaInv F m).toRingHom (proposedStarLinear (wedge u v)))
  simpa only [LinearMap.comp_apply, hw, traceZeroScalarMap_apply,
    LinearEquiv.coe_toLinearMap] using h

end Atlas.ReeF4

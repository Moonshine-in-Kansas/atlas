import Atlas.Fischer.IntrinsicTraceForm
import Atlas.Fischer.ExtremalReflectingRays

noncomputable section
namespace Atlas.Fischer

theorem semilinearAlgebra_rootMap (e : SemilinearAlgebraAutomorphism) (r x : Coordinates) :
    rootMap (e.val r) (e.val x) = e.val (rootMap r x) := by
  change rootMap (productTraceAlgebraEquiv e r) (productTraceAlgebraEquiv e x) =
    productTraceAlgebraEquiv e (rootMap r x)
  simp only [rootMap, map_sub, map_smulₛₗ]
  change product (e.val x) (e.val r) - hermitian (e.val r) (e.val x) • e.val r =
    e.val (product x r) - scalarParityAut (semilinearAlgebraParity e) (hermitian r x) • e.val r
  rw [semilinearAlgebraAutomorphism_hermitian, e.property.2.1]

theorem semilinearAlgebra_isRoot (e : SemilinearAlgebraAutomorphism)
    (r : Coordinates) (hr : IsRoot r) : IsRoot (e.val r) := by
  constructor
  · rw [semilinearAlgebraAutomorphism_hermitian, hr.1]
    exact map_ofNat _ _
  · rw [← e.property.2.1, hr.2, semilinearAlgebraParity_spec]
    congr 1
    exact map_ofNat _ _

theorem semilinearAlgebra_isReflectingRoot (e : SemilinearAlgebraAutomorphism)
    (r : Coordinates) (hr : IsReflectingRoot r) : IsReflectingRoot (e.val r) := by
  refine ⟨semilinearAlgebra_isRoot e r hr.1, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨x, rfl⟩ := e.val.surjective x
    obtain ⟨y, rfl⟩ := e.val.surjective y
    rw [semilinearAlgebra_rootMap, semilinearAlgebra_rootMap,
      semilinearAlgebraAutomorphism_hermitian, hr.2.1,
      semilinearAlgebraAutomorphism_hermitian, scalarParityAut_star]
  · intro x
    obtain ⟨x, rfl⟩ := e.val.surjective x
    rw [semilinearAlgebra_rootMap, semilinearAlgebra_rootMap, hr.2.2.1]
  · intro x y
    obtain ⟨x, rfl⟩ := e.val.surjective x
    obtain ⟨y, rfl⟩ := e.val.surjective y
    rw [← e.property.2.1, semilinearAlgebra_rootMap, hr.2.2.2,
      e.property.2.1, semilinearAlgebra_rootMap, semilinearAlgebra_rootMap]

theorem semilinearAlgebra_isReflectingRoot_iff (e : SemilinearAlgebraAutomorphism)
    (r : Coordinates) : IsReflectingRoot (e.val r) ↔ IsReflectingRoot r := by
  constructor
  · intro hr
    simpa using semilinearAlgebra_isReflectingRoot e⁻¹ (e.val r) hr
  · exact semilinearAlgebra_isReflectingRoot e r

/-- Every actual semilinear algebra automorphism
 preserves an extremal family as
normalized rays; the independent cardinal/injection premises remain explicit. -/
theorem extremalReflectingRays_automorphism {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hi : Function.Injective (fun j => rootRay (r j)))
    (hc : Fintype.card J = 306936) (e : SemilinearAlgebraAutomorphism) (j : J) :
    ∃ k, rootRay (e.val (r j)) = rootRay (r k) :=
  extremalReflectingRays_exhaust r hr hi hc _ (semilinearAlgebra_isReflectingRoot e _ (hr j))

end Atlas.Fischer


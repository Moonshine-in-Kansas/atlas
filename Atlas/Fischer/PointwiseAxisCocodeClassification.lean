import Atlas.Fischer.PointwiseAxisDuadFibre
import Atlas.Fischer.OctadResidualCocode
import Atlas.Fischer.PointwiseAxisFixedDuadSigns
import Atlas.Fischer.PointwiseAxisSignRelations
import Atlas.Fischer.GeneratedRayCocode

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private theorem algebra_eq_of_parity_basis (e f : SemilinearAlgebraAutomorphism)
    (hp : semilinearAlgebraParity e = semilinearAlgebraParity f)
    (hb : ∀ k, e.val (coordinateVector k) = f.val (coordinateVector k)) : e = f := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have hx : x = ∑ k : CoordinateIndex, x k • coordinateVector k := by
    simpa only [Pi.basisFun_repr, Pi.basisFun_apply, coordinateVector] using
      ((Pi.basisFun Scalar CoordinateIndex).sum_repr x).symm
  rw [hx]
  change productTraceAlgebraEquiv e _ = productTraceAlgebraEquiv f _
  simp only [map_sum, map_smulₛₗ]
  apply Finset.sum_congr rfl
  intro k _
  change scalarParityAut (semilinearAlgebraParity e) (x k) • e.val (coordinateVector k) = _
  rw [hp, hb k]
  rfl

private theorem algebra_eq_cocode_of_sign (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i) = u i) (d : Cocode)
    (hp : cocodeParity d = semilinearAlgebraParity e)
    (hs : ∀ D, cocodePairing (octadWord D) d = pointwiseAxisOctadSign e D) :
    e = cocodeAlgebraHom (Multiplicative.ofAdd d) := by
  apply algebra_eq_of_parity_basis
  · change semilinearAlgebraParity e = semilinearAlgebraParity
      (parkerAlgebraRepresentation (parkerCocodeStandard d))
    rw [parkerAlgebraRepresentation_parity, parkerStandardParity_cocode]
    exact hp.symm
  · intro k
    cases k with
    | inl i => exact (he i).trans (cocodeAlgebraHom_fixes_u _ i).symm
    | inr D =>
      rw [show coordinateVector (.inr D) = xOctad D from rfl,
        pointwiseAxisOctadSign_action e he D]
      change _ = cocodeCoordinateRepresentation (Multiplicative.ofAdd d) (coordinateVector (.inr D))
      rw [cocodeCoordinateRepresentation_basis]
      change _ = parkerScalarSign (cocodePairing (octadWord D) d) • xOctad D
      rw [hs D]

/-- A pointwise axis automorphism fixing an actual duadic root is already an
actual cocode operator. -/
theorem pointwiseAxis_fixed_duad_cocode (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i) = u i) (i j : Omega) (hij : i ≠ j)
    (ξ : Module.Dual Bit (duadShortenedCode ({i,j} : Finset Omega)))
    (hfix : e.val (chosenDuadicRoot ⟨{i,j}, by simp [hij]⟩ ξ) =
      chosenDuadicRoot ⟨{i,j}, by simp [hij]⟩ ξ) :
    ∃ d : Multiplicative Cocode, e = cocodeAlgebraHom d := by
  let p : RootDuad := ⟨{i,j}, by simp [hij]⟩
  obtain ⟨d,hp,hs⟩ := octad_residual_cocode i j hij (pointwiseAxisOctadSign e)
    (semilinearAlgebraParity e) (pointwiseAxisOctadSign_four e he)
    (fun D hi hj => pointwiseAxis_fixed_duad_avoiding e he p ξ hfix D (by
      change Disjoint ({i,j} : Finset Omega) D.val
      simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
      exact ⟨hi,hj⟩))
    (fun D hi hj => pointwiseAxis_fixed_duad_containing e he p ξ hfix D (by
      change ({i,j} : Finset Omega) ⊆ D.val
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hi,hj⟩))
  exact ⟨Multiplicative.ofAdd d, algebra_eq_cocode_of_sign e he d hp hs⟩

/-- The full actual pointwise axis stabilizer is precisely the cocode, uniquely. -/
theorem pointwiseAxis_unique_cocode (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i) = u i) :
    ∃! d : Multiplicative Cocode, e = cocodeAlgebraHom d := by
  classical
  obtain ⟨i,j,hij⟩ := exists_pair_ne Omega
  let p : RootDuad := ⟨{i,j}, by simp [hij]⟩
  obtain ⟨d,hd⟩ := pointwiseAxis_duadic_adjustment e he p 0
  let f := cocodeAlgebraHom (Multiplicative.ofAdd d) * e
  have hf : ∀ i, f.val (u i) = u i := by
    intro i
    change (cocodeAlgebraHom _).val (e.val (u i)) = u i
    rw [he i, cocodeAlgebraHom_fixes_u]
  have hfix : f.val (chosenDuadicRoot p 0) = chosenDuadicRoot p 0 := hd
  obtain ⟨c,hc⟩ := pointwiseAxis_fixed_duad_cocode f hf i j hij 0 hfix
  have heq : e = cocodeAlgebraHom ((Multiplicative.ofAdd d)⁻¹ * c) := by
    rw [map_mul, map_inv, ← hc]
    change e = (cocodeAlgebraHom (Multiplicative.ofAdd d))⁻¹ *
      (cocodeAlgebraHom (Multiplicative.ofAdd d) * e)
    simp
  refine ⟨_, heq, ?_⟩
  intro c' hc'
  exact cocodeAlgebraHom_injective (hc'.symm.trans heq)

end Atlas.Fischer

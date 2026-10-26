import Atlas.LinearGroups.Chevalley.Comparison.TypeBOrthogonalHom
import Atlas.LinearGroups.Chevalley.WeightCompanionOrbitCenterScalar

/-! The full center acts by actual scalar spin matrices and hence trivially
on the odd vector space, including in characteristic two and at B2(F2). -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeB
open Classical ClassicalData Integral.Minuscule
variable (n : ℕ) (hn : 2 ≤ n+1) (K : Type*) [Field K] [Finite K]

theorem spinMatrixHom_center_scalar
    (g : SelectedWeightCompanion (.B (n+1) hn) K)
    (hg : g ∈ Subgroup.center (SelectedWeightCompanion (.B (n+1) hn) K)) :
    ∃ c : Kˣ, spinMatrixHom n hn K g = (c : K) • 1 := by
  have hs := weightCompanion_center_minuscule_scalar
    (rootDatum (.B (n+1) hn)).pairing (rootDatum (.B (n+1) hn)).base
    (selectedWeightOrbits (.B (n+1) hn))
    (selectedWeightOrbits_closed (.B (n+1) hn))
    (selectedWeightOrbits_minuscule (.B (n+1) hn)) K
    (rootDatum_simpleDiamondProducts (.B (n+1) hn)) ()
    (spinLabel n (fun _ => false)) (fun μ =>
      Integral.Minuscule.TypeB.spinOrbit_transitive n _ _
        (spinLabel n (fun _ => false)).property μ.property) g hg
  obtain ⟨c,hc⟩ := hs
  refine ⟨c, ?_⟩
  change spinReindex n K (g.val.2 ()).val = _
  rw [hc]
  have hmap : spinReindex n K ((c : K) • 1) = (c : K) • 1 := by
    simp only [map_smul, map_one]
  exact hmap

/-- The full source center lies in the kernel of the concrete elementary map.
No target simplicity, source order or kernel-cardinality argument is used. -/
theorem center_le_elementaryHom_ker :
    Subgroup.center (SelectedWeightCompanion (.B (n+1) hn) K) ≤
      (elementaryHom n hn K).ker := by
  intro g hg
  change elementaryHom n hn K g = 1
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change (orthogonalHom n hn K g).val v = v
  apply spinMatrixGamma_injective n K
  rw [← orthogonalHom_gamma]
  obtain ⟨c,hc⟩ := spinMatrixHom_center_scalar n hn K g hg
  have hcomm : spinMatrixHom n hn K g * spinMatrixGamma n K v =
      spinMatrixGamma n K v * spinMatrixHom n hn K g := by
    rw [hc]
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [hcomm, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

end Atlas.Chevalley.Comparison.TypeB

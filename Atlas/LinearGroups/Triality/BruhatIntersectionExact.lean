import Atlas.LinearGroups.Triality.BruhatIntersection

/-! Exact coordinate description of the intersection with a conjugate Borel. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

theorem shortSigned_conjugate_mem (w : Fin 12) (i : Fin 6) (t : K)
    (hz : ¬ (shortSignedWord (weylWord w) i).val < 3 → t=0) :
    (weylLift F K w)⁻¹ * shortSignedRoot F K i t * weylLift F K w ∈ borel F K hdeg := by
  by_cases hp : (shortSignedWord (weylWord w) i).val < 3
  · obtain ⟨u,hu⟩ := shortSignedWord_conjugate F K (weylWord w) i t
    change (weylLift F K w)⁻¹ * shortSignedRoot F K i t * weylLift F K w = _ at hu
    rw [hu]
    exact unipotent_le_borel F K hdeg (shortSignedRoot_positive F K hdeg _ hp u)
  · rw [hz hp]
    have hzero : shortSignedRoot F K i 0=1 := by
      fin_cases i <;> simp [shortSignedRoot, nextNegativeRoot, middleNegativeRoot,
        highNegativeRoot, highestNegativeRoot]
      all_goals
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        simp [Subgroup.coe_mul, LinearEquiv.mul_apply, differenceRoot_apply, negativeSumRoot_apply]
    simp [hzero]

theorem longSigned_conjugate_mem (w : Fin 12) (i : Fin 6) (t : F)
    (hz : ¬ (longSignedWord (weylWord w) i).val < 3 → t=0) :
    (weylLift F K w)⁻¹ * longSignedRoot F K i t * weylLift F K w ∈ borel F K hdeg := by
  by_cases hp : (longSignedWord (weylWord w) i).val < 3
  · obtain ⟨u,hu⟩ := longSignedWord_conjugate F K (weylWord w) i t
    change (weylLift F K w)⁻¹ * longSignedRoot F K i t * weylLift F K w = _ at hu
    rw [hu]
    exact unipotent_le_borel F K hdeg (longSignedRoot_positive F K hdeg _ hp u)
  · rw [hz hp]
    have hzero : longSignedRoot F K i 0=1 := by
      fin_cases i <;> simp [longSignedRoot, nextNegativeRoot, middleNegativeRoot,
        highNegativeRoot, highestNegativeRoot]
      all_goals
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        simp [Subgroup.coe_mul, LinearEquiv.mul_apply, differenceRoot_apply, negativeSumRoot_apply]
    simp [hzero]

theorem positive_conjugate_of_surviving (w : Fin 12) (p : PositiveParameters F K)
    (hp : SurvivingParameters F K w p) :
    (weylLift F K w)⁻¹ * positiveMatrix F K p * weylLift F K w ∈ borel F K hdeg := by
  let H := (borel F K hdeg).comap (MulAut.conj ((weylLift F K w)⁻¹)).toMonoidHom
  have hm (g : O_DPlus 4 K) : g ∈ H ↔
      (weylLift F K w)⁻¹*g*weylLift F K w ∈ borel F K hdeg := by
    simp [H, MulAut.conj_apply]
  have ha : shortRoot F K p.a ∈ H := by
    rw [hm]
    exact shortSigned_conjugate_mem F K hdeg w 0 p.a (fun hn => hp.1 (by simpa [rootSurvives] using hn))
  have hb : longRoot F K p.b ∈ H := by
    rw [hm]
    exact longSigned_conjugate_mem F K hdeg w 0 p.b (fun hn => hp.2.1 (by simpa [rootSurvives] using hn))
  have hc : nextShortRoot F K p.c ∈ H := by
    rw [hm]
    exact shortSigned_conjugate_mem F K hdeg w 1 p.c (fun hn => hp.2.2.1 (by simpa [rootSurvives] using hn))
  have hd : middleRoot F K p.d ∈ H := by
    rw [hm]
    exact shortSigned_conjugate_mem F K hdeg w 2 p.d (fun hn => hp.2.2.2.1 (by simpa [rootSurvives] using hn))
  have hu : highLongRoot F K p.u ∈ H := by
    rw [hm]
    exact longSigned_conjugate_mem F K hdeg w 1 p.u (fun hn => hp.2.2.2.2.1 (by simpa [rootSurvives] using hn))
  have hv : highestRoot F K p.v ∈ H := by
    rw [hm]
    exact longSigned_conjugate_mem F K hdeg w 2 p.v (fun hn => hp.2.2.2.2.2 (by simpa [rootSurvives] using hn))
  exact (hm _).mp (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem ha hb) hc) hd) hu) hv)

theorem positive_conjugate_iff (w : Fin 12) (p : PositiveParameters F K) :
    (weylLift F K w)⁻¹ * positiveMatrix F K p * weylLift F K w ∈ borel F K hdeg ↔
      SurvivingParameters F K w p :=
  ⟨survivingParameters_of_conjugate F K hdeg w p,positive_conjugate_of_surviving F K hdeg w p⟩

theorem borelWord_conjugate_iff (w : Fin 12) (p : PositiveParameters F K) (h : Kˣ × Fˣ) :
    (weylLift F K w)⁻¹ * borelWord F K p h * weylLift F K w ∈ borel F K hdeg ↔
      SurvivingParameters F K w p := by
  have hh : (weylLift F K w)⁻¹ * torusMap F K h * weylLift F K w ∈ borel F K hdeg := by
    apply torus_le_borel F K hdeg
    have hn := (Subgroup.normalizer (torus F K : Set (O_DPlus 4 K))).inv_mem
      (weylLift_normalizes_torus F K hdeg w)
    simpa only [inv_inv] using ((Subgroup.mem_normalizer_iff.mp hn) (torusMap F K h)).mp ⟨h,rfl⟩
  rw [← positive_conjugate_iff F K hdeg w p]
  have he : (weylLift F K w)⁻¹ * borelWord F K p h * weylLift F K w =
      ((weylLift F K w)⁻¹ * positiveMatrix F K p * weylLift F K w) *
        ((weylLift F K w)⁻¹ * torusMap F K h * weylLift F K w) := by
    unfold borelWord
    group
  rw [he]
  exact (borel F K hdeg).mul_mem_cancel_right hh

end Atlas.Triality

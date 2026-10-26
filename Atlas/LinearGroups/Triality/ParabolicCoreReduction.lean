import Atlas.LinearGroups.Triality.ParabolicRootCells
import Atlas.LinearGroups.Triality.BruhatIntersectionExact

/-! Any subgroup normal under the generated group and contained in the long
 parabolic is confined first to B, then to its actual diagonal torus. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

theorem firstLine_coordinate_zero {x : VectorD 4 K} (hx : x ∈ firstLine K)
    (i : Index 4) (hi : i ≠ .inl 0) : x i=0 := by
  have hle : firstLine K ≤ LinearMap.ker (LinearMap.proj i : VectorD 4 K →ₗ[K] K) := by
    apply Submodule.span_le.mpr
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    simpa [LinearMap.mem_ker,e,Pi.single_apply,hi,Ne.symm hi]
  exact hle hx

theorem shortWeyl_inv_e_zero : (shortWeyl F K)⁻¹.val (e 0) = e 1 := by
  have he : (shortWeyl F K).val (e 1)=e 0 := by
    ext i
    rcases i with i|i <;> fin_cases i <;> simp [shortWeyl_apply,e]
  change (shortWeyl F K).val.symm (e 0)=e 1
  rw [← he]
  exact (shortWeyl F K).val.symm_apply_apply _

theorem longRootCell_entry (t : F) (b : borel F K hdeg) :
    (longRoot F K t * longWeyl F K * b.val).val (e 1) (.inl 2) =
      -b.val.val (e 1) (.inl 1) := by
  simp [Subgroup.coe_mul,LinearEquiv.mul_apply,longRoot,pinnedRoot,
    differenceRoot_apply,longWeyl_apply,e,f,Algebra.smul_def]

theorem normal_in_longParabolic_le_borel (N : Subgroup (O_DPlus 4 K))
    (hNP : N ≤ longParabolic F K hdeg)
    (hconj : ∀ a ∈ generated F K, ∀ g ∈ N, a*g*a⁻¹ ∈ N) : N ≤ borel F K hdeg := by
  intro g hg
  have hc := hNP (hconj (shortWeyl F K) (shortWeyl_mem F K) g hg)
  have hl := (spaceStabilizer_mem K _ _).mp (longParabolic_stabilizes_line F K hdeg hc)
    (e 0) (Submodule.subset_span (Set.mem_singleton _))
  have hz := firstLine_coordinate_zero K hl (.inr 2) (by decide)
  change (shortWeyl F K).val (g.val ((shortWeyl F K)⁻¹.val (e 0))) (.inr 2)=0 at hz
  rw [shortWeyl_inv_e_zero,shortWeyl_apply] at hz
  have hgzero : g.val (e 1) (.inl 2)=0 := by simpa using hz
  rcases longParabolic_root_cell F K hdeg g (hNP hg) with hb | ⟨t,b,he⟩
  · exact hb
  · rw [he,longRootCell_entry F K hdeg] at hgzero
    have hn := borel_diagonal_ne_zero F K hdeg b (.inl 1)
    exact False.elim (hn (by simpa [e] using hgzero))

theorem borel_opposite_intersection_le_torus (g : O_DPlus 4 K)
    (hg : g ∈ borel F K hdeg)
    (ho : (weylLift F K 11)⁻¹*g*weylLift F K 11 ∈ borel F K hdeg) : g ∈ torus F K := by
  obtain ⟨⟨p,h⟩,he⟩ := hg
  change borelWord F K p h=g at he
  rw [← he] at ho
  have hp := (borelWord_conjugate_iff F K hdeg 11 p h).mp ho
  have ha := hp.1 (by decide)
  have hb := hp.2.1 (by decide)
  have hc := hp.2.2.1 (by decide)
  have hd := hp.2.2.2.1 (by decide)
  have hu := hp.2.2.2.2.1 (by decide)
  have hv := hp.2.2.2.2.2 (by decide)
  rw [← he]
  have hz : p=⟨0,0,0,0,0,0⟩ := by cases p; simp_all
  rw [hz]
  simpa [borelWord,positiveMatrix_zero] using (show torusMap F K h ∈ torus F K from ⟨h,rfl⟩)

theorem normal_in_longParabolic_le_torus (N : Subgroup (O_DPlus 4 K))
    (hNP : N ≤ longParabolic F K hdeg)
    (hconj : ∀ a ∈ generated F K, ∀ g ∈ N, a*g*a⁻¹ ∈ N) : N ≤ torus F K := by
  have hB := normal_in_longParabolic_le_borel F K hdeg N hNP hconj
  intro g hg
  apply borel_opposite_intersection_le_torus F K hdeg g (hB hg)
  have hw : weylLift F K 11 ∈ generated F K := by
    apply weylSubgroup_le_generated F K hdeg
    exact ⟨(11,1),by simp [weylTorusWord]⟩
  have hc := hconj ((weylLift F K 11)⁻¹) ((generated F K).inv_mem hw) g hg
  exact hB (by simpa only [inv_inv] using hc)

end Atlas.Triality

import Atlas.LinearGroups.Triality.ParabolicBasic
import Mathlib.Algebra.Pointwise.Stabilizer

/-! Properness of the actual parabolics from the first isotropic line and plane.
This is independent of the still outstanding maximality and action-kernel proofs. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
open scoped Pointwise
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def firstLine : Submodule K (VectorD 4 K) := Submodule.span K {e 0}
def firstPlane : Submodule K (VectorD 4 K) := Submodule.span K {e 0, e 1}

def spaceStabilizer (W : Submodule K (VectorD 4 K)) : Subgroup (O_DPlus 4 K) :=
  (MulAction.stabilizer (VectorD 4 K ≃ₗ[K] VectorD 4 K) (W : Set (VectorD 4 K))).comap
    (isometrySubgroup (formD 4 K)).subtype

theorem spaceStabilizer_mem (W : Submodule K (VectorD 4 K)) (g : O_DPlus 4 K) :
    g ∈ spaceStabilizer K W ↔ ∀ x ∈ W, g.val x ∈ W := by
  exact MulAction.mem_stabilizer_set' (Set.toFinite _)

private theorem firstLine_contains : e (0 : Fin 4) ∈ firstLine K :=
  Submodule.subset_span (Set.mem_singleton _)

private theorem firstPlane_contains_zero : e (0 : Fin 4) ∈ firstPlane K :=
  Submodule.subset_span (by simp)
private theorem firstPlane_contains_one : e (1 : Fin 4) ∈ firstPlane K :=
  Submodule.subset_span (by simp)

theorem positiveMatrix_e_zero (p : PositiveParameters F K) :
    (positiveMatrix F K p).val (e 0) = e 0 := by
  change (positiveWord F K p.a p.b p.c p.d p.u p.v).val (e 0) = e 0
  rw [positiveWord_apply]
  ext i
  rcases i with i|i <;> fin_cases i <;> simp [positiveAction, e]

theorem positiveMatrix_e_one (p : PositiveParameters F K) :
    (positiveMatrix F K p).val (e 1) = p.a • e 0 + e 1 := by
  change (positiveWord F K p.a p.b p.c p.d p.u p.v).val (e 1) = _
  rw [positiveWord_apply]
  ext i
  rcases i with i|i <;> fin_cases i <;> simp [positiveAction, e]

theorem torus_e (h : Kˣ × Fˣ) (j : Fin 4) :
    (torusMap F K h).val (e j) = (torusWeights F K h j : K) • e j := by
  ext i
  rcases i with i|i <;>
    simp [torusMap, diagonalEmbedding, diagonalLinear, e, Pi.single_apply]
  split_ifs <;> simp_all

private theorem stabilizes_span (S : Set (VectorD 4 K)) (g : O_DPlus 4 K)
    (hg : ∀ x ∈ S, g.val x ∈ Submodule.span K S) :
    g ∈ spaceStabilizer K (Submodule.span K S) := by
  apply (spaceStabilizer_mem K _ g).mpr
  change Submodule.span K S ≤ (Submodule.span K S).comap g.val.toLinearMap
  exact Submodule.span_le.mpr hg

theorem unipotent_stabilizes_line (hdeg : Module.finrank F K = 3) :
    unipotent F K hdeg ≤ spaceStabilizer K (firstLine K) := by
  rintro _ ⟨p,rfl⟩
  apply stabilizes_span K
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  rw [positiveMatrix_e_zero]
  exact firstLine_contains K

theorem unipotent_stabilizes_plane (hdeg : Module.finrank F K = 3) :
    unipotent F K hdeg ≤ spaceStabilizer K (firstPlane K) := by
  rintro _ ⟨p,rfl⟩
  apply stabilizes_span K
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · rw [positiveMatrix_e_zero]
    exact firstPlane_contains_zero K
  · rcases Set.mem_singleton_iff.mp hx with rfl
    rw [positiveMatrix_e_one]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (firstPlane_contains_zero K)) (firstPlane_contains_one K)

theorem torus_stabilizes_line : torus F K ≤ spaceStabilizer K (firstLine K) := by
  rintro _ ⟨h,rfl⟩
  apply stabilizes_span K
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  rw [torus_e]
  exact Submodule.smul_mem _ _ (firstLine_contains K)

theorem torus_stabilizes_plane : torus F K ≤ spaceStabilizer K (firstPlane K) := by
  rintro _ ⟨h,rfl⟩
  apply stabilizes_span K
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · rw [torus_e]
    exact Submodule.smul_mem _ _ (firstPlane_contains_zero K)
  · rcases Set.mem_singleton_iff.mp hx with rfl
    rw [torus_e]
    exact Submodule.smul_mem _ _ (firstPlane_contains_one K)

theorem longWeyl_stabilizes_line : longWeyl F K ∈ spaceStabilizer K (firstLine K) := by
  apply stabilizes_span K
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  have he : (longWeyl F K).val (e 0) = e 0 := by
    ext i
    rcases i with i|i <;> fin_cases i <;> simp [longWeyl_apply, e]
  rw [he]
  exact firstLine_contains K

theorem shortWeyl_stabilizes_plane : shortWeyl F K ∈ spaceStabilizer K (firstPlane K) := by
  apply stabilizes_span K
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · have he : (shortWeyl F K).val (e 0) = -e 1 := by
      ext i
      rcases i with i|i <;> fin_cases i <;> simp [shortWeyl_apply, e]
    rw [he]
    exact Submodule.neg_mem _ (firstPlane_contains_one K)
  · rcases Set.mem_singleton_iff.mp hx with rfl
    have he : (shortWeyl F K).val (e 1) = e 0 := by
      ext i
      rcases i with i|i <;> fin_cases i <;> simp [shortWeyl_apply, e]
    rw [he]
    exact firstPlane_contains_zero K

theorem longParabolic_stabilizes_line (hdeg : Module.finrank F K = 3) :
    longParabolic F K hdeg ≤ spaceStabilizer K (firstLine K) := by
  apply sup_le
  · rw [borel_eq_sup]
    exact sup_le (unipotent_stabilizes_line F K hdeg) (torus_stabilizes_line F K)
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact longWeyl_stabilizes_line F K

theorem shortParabolic_stabilizes_plane (hdeg : Module.finrank F K = 3) :
    shortParabolic F K hdeg ≤ spaceStabilizer K (firstPlane K) := by
  apply sup_le
  · rw [borel_eq_sup]
    exact sup_le (unipotent_stabilizes_plane F K hdeg) (torus_stabilizes_plane F K)
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact shortWeyl_stabilizes_plane F K

theorem firstLine_coordinate_one_zero {x : VectorD 4 K} (hx : x ∈ firstLine K) :
    x (.inl 1) = 0 := by
  have hle : firstLine K ≤ LinearMap.ker (LinearMap.proj (.inl 1) : VectorD 4 K →ₗ[K] K) := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change (e (0 : Fin 4) : VectorD 4 K) (.inl 1) = 0
    simp [e]
  exact hle hx

theorem firstPlane_coordinate_two_zero {x : VectorD 4 K} (hx : x ∈ firstPlane K) :
    x (.inl 2) = 0 := by
  have hle : firstPlane K ≤ LinearMap.ker (LinearMap.proj (.inl 2) : VectorD 4 K →ₗ[K] K) := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · change (e (0 : Fin 4) : VectorD 4 K) (.inl 2) = 0
      simp [e]
    · rcases Set.mem_singleton_iff.mp hx with rfl
      change (e (1 : Fin 4) : VectorD 4 K) (.inl 2) = 0
      simp [e]
  exact hle hx

theorem shortWeyl_not_mem_longParabolic (hdeg : Module.finrank F K = 3) :
    shortWeyl F K ∉ longParabolic F K hdeg := by
  intro hg
  have hh := (spaceStabilizer_mem K _ _).mp (longParabolic_stabilizes_line F K hdeg hg)
    (e 0) (firstLine_contains K)
  have hz := firstLine_coordinate_one_zero K hh
  simpa [shortWeyl_apply, e] using hz

theorem longWeyl_not_mem_shortParabolic (hdeg : Module.finrank F K = 3) :
    longWeyl F K ∉ shortParabolic F K hdeg := by
  intro hg
  have hh := (spaceStabilizer_mem K _ _).mp (shortParabolic_stabilizes_plane F K hdeg hg)
    (e 1) (firstPlane_contains_one K)
  have hz := firstPlane_coordinate_two_zero K hh
  simpa [longWeyl_apply, e] using hz

theorem longParabolic_lt_generated (hdeg : Module.finrank F K = 3) :
    longParabolic F K hdeg < generated F K := by
  refine lt_of_le_of_ne (longParabolic_le_generated F K hdeg) ?_
  intro he
  apply shortWeyl_not_mem_longParabolic F K hdeg
  rw [he]
  exact shortWeyl_mem F K

theorem shortParabolic_lt_generated (hdeg : Module.finrank F K = 3) :
    shortParabolic F K hdeg < generated F K := by
  refine lt_of_le_of_ne (shortParabolic_le_generated F K hdeg) ?_
  intro he
  apply longWeyl_not_mem_shortParabolic F K hdeg
  rw [he]
  exact longWeyl_mem F K

end Atlas.Triality


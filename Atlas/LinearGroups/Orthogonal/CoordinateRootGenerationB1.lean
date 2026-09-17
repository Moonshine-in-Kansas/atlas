import Atlas.LinearGroups.Orthogonal.CoordinateRootGeneration
import Atlas.LinearGroups.Orthogonal.CoordinateRootSubgroups
import Atlas.LinearGroups.Orthogonal.B1ConjugationImage

noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic Matrix
variable {F : Type*} [Field F]

theorem B1_conjugation_mem_coordinate (g : B1Conjugation.SL (F := F)) :
    B1Conjugation.toOrthogonal g ∈ coordinateRootSubgroupB (F := F) 1 := by
  apply Atlas.sl_elementary_induction (fun g => B1Conjugation.toOrthogonal g ∈ coordinateRootSubgroupB 1) ?_
    (fun a b ha hb => by rw [map_mul]; exact (coordinateRootSubgroupB 1).mul_mem ha hb) g
  intro i j hij a
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · have hv : (formB 1 F).polarBilin (e 0,0) (0,-a)=0 := by
      rw [polarB_apply]; simp
    have he := B1Conjugation.standard_siegel_image (F := F) (0,-a) hv
    simp only [neg_neg] at he
    rw [←he]
    apply rootB_e_le_coordinate 1 0
    exact ⟨Multiplicative.ofAdd ⟨(0,-a),hv⟩,rfl⟩
  · rw [B1Conjugation.lower_transvection_root]
    apply rootB_f_le_coordinate 1 0
    exact ⟨Multiplicative.ofAdd ⟨(0,a),by change (formB 1 F).polarBilin (f 0,0) (0,a)=0; rw [polarB_apply]; simp⟩,rfl⟩
  · exact (hij rfl).elim

theorem coordinateRootSubgroupB_one_eq_elementary :
    coordinateRootSubgroupB (F := F) 1 = elementarySubgroup (formB 1 F) := by
  apply le_antisymm (coordinateRootSubgroupB_le_elementary 1)
  rw [←B1Conjugation.toOrthogonal_range]
  rintro g ⟨a,rfl⟩
  exact B1_conjugation_mem_coordinate a

end Atlas.Orthogonal

namespace Atlas.Orthogonal
variable {F : Type*} [Field F]

/-- Coordinate-root generation in every positive odd-dimensional rank, including rank one and all characteristics. -/
theorem coordinateRootSubgroupB_eq_elementary_of_pos (n : ℕ) (hn : 0<n) :
    coordinateRootSubgroupB (F := F) n = elementarySubgroup (formB n F) := by
  by_cases he : n=1
  · subst n
    exact coordinateRootSubgroupB_one_eq_elementary
  · exact coordinateRootSubgroupB_eq_elementary n (by omega)

end Atlas.Orthogonal

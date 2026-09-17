import Atlas.LinearGroups.Orthogonal.RootCoordinateExpansion
import Atlas.LinearGroups.Orthogonal.StandardComplement
import Mathlib.LinearAlgebra.Basis.Prod

noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic Module
variable {F : Type*} [Field F]

def coordinateBasisD (n : ℕ) : Basis (Index n) F (VectorD n F) := Pi.basisFun F (Index n)
def coordinateBasisB (n : ℕ) : Basis (Index n ⊕ Unit) F (VectorB n F) :=
  (coordinateBasisD n).prod (Basis.singleton Unit F)

def coordinateRootSubgroupD (n : ℕ) : Subgroup (O_DPlus n F) :=
  coordinateRootSubgroup (formD n F) (coordinateBasisD n)

def coordinateRootSubgroupB (n : ℕ) : Subgroup (O_B n F) :=
  coordinateRootSubgroup (formB n F) (coordinateBasisB n)

theorem coordinateRootSubgroupD_le_elementary (n : ℕ) :
    coordinateRootSubgroupD (F := F) n ≤ elementarySubgroup (formD n F) :=
  coordinateRootSubgroup_le_elementary _ _

theorem coordinateRootSubgroupB_le_elementary (n : ℕ) :
    coordinateRootSubgroupB (F := F) n ≤ elementarySubgroup (formB n F) :=
  coordinateRootSubgroup_le_elementary _ _


theorem rootD_e_le_coordinate (n : ℕ) (i : Fin n) :
    rootSubgroup (formD n F) (e i) (formD_e i) ≤ coordinateRootSubgroupD (F := F) n := by
  apply coordinate_root_le_of_coefficient_vanishing (formD n F) (coordinateBasisD n)
    (.inl i) (e i) (formD_e i) (by simp [coordinateBasisD,e])
  intro v hv j hj
  rw [polar_swap,polarD_e] at hv
  rw [polar_swap,polarD_e] at hj
  have he : j = .inr i := by
    by_contra hn
    exact hj (by simp [coordinateBasisD,Pi.basisFun_apply,Pi.single_apply,Ne.symm hn])
  subst j
  simpa [coordinateBasisD] using hv

theorem rootD_f_le_coordinate (n : ℕ) (i : Fin n) :
    rootSubgroup (formD n F) (f i) (formD_f i) ≤ coordinateRootSubgroupD (F := F) n := by
  apply coordinate_root_le_of_coefficient_vanishing (formD n F) (coordinateBasisD n)
    (.inr i) (f i) (formD_f i) (by simp [coordinateBasisD,f])
  intro v hv j hj
  rw [polar_swap,polarD_f] at hv
  rw [polar_swap,polarD_f] at hj
  have he : j = .inl i := by
    by_contra hn
    exact hj (by simp [coordinateBasisD,Pi.basisFun_apply,Pi.single_apply,Ne.symm hn])
  subst j
  simpa [coordinateBasisD] using hv

theorem rootB_e_le_coordinate (n : ℕ) (i : Fin n) :
    rootSubgroup (formB n F) (e i,0) (by simp [e]) ≤ coordinateRootSubgroupB (F := F) n := by
  apply coordinate_root_le_of_coefficient_vanishing (formB n F) (coordinateBasisB n)
    (.inl (.inl i)) (e i,0) (by simp [e]) (by simp [coordinateBasisB,coordinateBasisD,e])
  intro v hv j hj
  have hv' : v.1 (.inr i)=0 := by
    rw [polar_swap,polarB_apply,polarD_e] at hv
    simpa using hv
  rw [polar_swap,polarB_apply,polarD_e] at hj
  simp only [mul_zero,add_zero] at hj
  cases j with
  | inl j =>
    have he : j = .inr i := by
      by_contra hn
      exact hj (by simp [coordinateBasisB,coordinateBasisD,Pi.basisFun_apply,Pi.single_apply,Ne.symm hn])
    subst j
    simpa [coordinateBasisB,coordinateBasisD] using hv'
  | inr j =>
    exact False.elim (hj (by simp [coordinateBasisB]))

theorem rootB_f_le_coordinate (n : ℕ) (i : Fin n) :
    rootSubgroup (formB n F) (f i,0) (by simp [f]) ≤ coordinateRootSubgroupB (F := F) n := by
  apply coordinate_root_le_of_coefficient_vanishing (formB n F) (coordinateBasisB n)
    (.inl (.inr i)) (f i,0) (by simp [f]) (by simp [coordinateBasisB,coordinateBasisD,f])
  intro v hv j hj
  have hv' : v.1 (.inl i)=0 := by
    rw [polar_swap,polarB_apply,polarD_f] at hv
    simpa using hv
  rw [polar_swap,polarB_apply,polarD_f] at hj
  simp only [mul_zero,add_zero] at hj
  cases j with
  | inl j =>
    have he : j = .inl i := by
      by_contra hn
      exact hj (by simp [coordinateBasisB,coordinateBasisD,Pi.basisFun_apply,Pi.single_apply,Ne.symm hn])
    subst j
    simpa [coordinateBasisB,coordinateBasisD] using hv'
  | inr j =>
    exact False.elim (hj (by simp [coordinateBasisB]))

end Atlas.Orthogonal

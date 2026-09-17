import Atlas.LinearAlgebra.QuadraticDicksonReflection
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The residual space of a Siegel transformation -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (u v : V) (hu : Q u = 0)
  (huv : Q.polarBilin u v = 0)

theorem siegel_residual_le_span :
    residual Q (siegelIsometry Q u v hu huv) ≤ Submodule.span F {u, v} := by
  rintro x ⟨y, rfl⟩
  have he : residualMap Q (siegelIsometry Q u v hu huv) y =
      (Q v * Q.polarBilin y u - Q.polarBilin y v) • u +
        Q.polarBilin y u • v := by
    change y - siegel Q u v y = _
    unfold siegel
    module
  rw [he]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem siegel_isotropic_residual (hv : Q v = 0)
    (x : residual Q (siegelIsometry Q u v hu huv)) : Q x.val = 0 := by
  obtain ⟨y, hy⟩ := x.prop
  change y - siegel Q u v y = x.val at hy
  rw [← hy]
  have he : y - siegel Q u v y =
      (-Q.polarBilin y v) • u + Q.polarBilin y u • v := by
    simp only [siegel, hv, zero_mul, zero_smul, sub_zero]
    module
  rw [he, QuadraticMap.map_add Q]
  change _ + _ + Q.polarBilin ((-Q.polarBilin y v) • u) (Q.polarBilin y u • v) = 0
  simp only [Q.map_smul, hu, hv, map_smul, LinearMap.smul_apply,
    huv, smul_zero, add_zero]

variable [FiniteDimensional F V]

theorem siegel_residual_finrank_le_two :
    Module.finrank F (residual Q (siegelIsometry Q u v hu huv)) ≤ 2 := by
  calc
    _ ≤ Module.finrank F (Submodule.span F ({u, v} : Set V)) :=
      Submodule.finrank_mono (siegel_residual_le_span Q u v hu huv)
    _ ≤ 2 := by
      classical
      have h := finrank_span_le_card (R := F) ({u, v} : Set V)
      exact h.trans (by simpa using Finset.card_insert_le u ({v} : Finset V))

theorem dicksonParity_siegel_isotropic (hQ : Q.polarBilin.Nondegenerate)
    (hv : Q v = 0) : dicksonParity Q (siegelIsometry Q u v hu huv) = 0 := by
  let S := residual Q (siegelIsometry Q u v hu huv)
  have hle := siegel_residual_finrank_le_two Q u v hu huv
  have hn : Module.finrank F S ≠ 1 := by
    intro h
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
      (show 0 < Module.finrank F S by omega)
    apply hx
    apply (wallForm_nondegenerate Q (siegelIsometry Q u v hu huv) hQ).1
    intro y
    obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one h hx y
    rw [map_smul, wallForm_self, siegel_isotropic_residual Q u v hu huv hv, smul_zero]
  change (Module.finrank F S : ZMod 2) = 0
  have hd : Module.finrank F S = 0 ∨ Module.finrank F S = 2 := by
    change Module.finrank F S ≤ 2 at hle
    omega
  rcases hd with hd | hd <;> rw [hd] <;> decide
end Atlas.Quadratic

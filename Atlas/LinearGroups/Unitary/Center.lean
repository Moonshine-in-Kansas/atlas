import Atlas.LinearGroups.Unitary.ScalarSubgroup
import Atlas.LinearGroups.Unitary.CenterLines
import Atlas.LinearGroups.Unitary.IsotropicScalar

/-! # The full special unitary center

Central elements preserve each isotropic line by centralizing genuine
transvections. The coordinate-plane polynomial argument then makes them scalar.
The argument is uniform in all finite characteristics and does not use group
order, generation, perfectness, or simplicity.
-/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

theorem central_matrix_scalar (hdeg : Module.finrank F K = 2) (hn : 0 < n)
    (g : SU F K n hdeg) (hg : g ∈ Subgroup.center (SU F K n hdeg)) :
    ∃ c : K, g.val = Matrix.diagonal (fun _ => c) :=
  matrix_scalar_of_isotropic_lines hdeg hn g.val
    (central_preserves_isotropic_lines hdeg g hg)

/-- Any scalar matrix in the actual special unitary carrier has precisely the
norm and power conditions defining the scalar parameter group. -/
theorem scalar_matrix_parameter (hdeg : Module.finrank F K = 2) (hn : 0 < n)
    (g : SU F K n hdeg) (c : K) (hc : g.val = Matrix.diagonal (fun _ => c)) :
    ∃ a : scalarParameters F K n, scalarSpecial F K hdeg a = g := by
  let i : Fin n := ⟨0, hn⟩
  have hnorm : c * conjugation F K c = 1 := by
    have h := u_preserves_hermitian hdeg (⟨g.val, g.prop.1⟩ : U F K n hdeg)
      (Pi.single i 1) (Pi.single i 1)
    change hermitian F K (g.val *ᵥ Pi.single i 1) (g.val *ᵥ Pi.single i 1) = _ at h
    rw [hc] at h
    simpa [Matrix.mulVec_diagonal, hermitian, Pi.single_apply] using h
  have hc0 : c ≠ 0 := by
    intro he
    simp [he] at hnorm
  let a : normOne F K := ⟨Units.mk0 c hc0, (normOne_mem_iff hdeg _).mpr hnorm⟩
  have ha : a ^ n = 1 := by
    apply Subtype.ext
    apply Units.ext
    have hdet : g.val.det = 1 := g.prop.2
    rw [hc, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    exact hdet
  refine ⟨⟨a, ha⟩, ?_⟩
  apply Subtype.ext
  exact hc.symm

theorem scalarCenterHom_surjective (hdeg : Module.finrank F K = 2) (hn : 0 < n) :
    Function.Surjective (scalarCenterHom F K hdeg n) := by
  intro g
  obtain ⟨c, hc⟩ := central_matrix_scalar hdeg hn g.val g.prop
  obtain ⟨a, ha⟩ := scalar_matrix_parameter hdeg hn g.val c hc
  exact ⟨a, Subtype.ext ha⟩

/-- The full center, retaining its inclusion in the actual SU carrier. -/
def scalarCenterEquiv (hdeg : Module.finrank F K = 2) (hn : 0 < n) :
    scalarParameters F K n ≃* Subgroup.center (SU F K n hdeg) :=
  MulEquiv.ofBijective (scalarCenterHom F K hdeg n)
    ⟨scalarCenterHom_injective F K hdeg hn, scalarCenterHom_surjective hdeg hn⟩

theorem center_eq_scalarSubgroup (hdeg : Module.finrank F K = 2) (hn : 0 < n) :
    Subgroup.center (SU F K n hdeg) = scalarSubgroup F K hdeg n := by
  apply le_antisymm
  · intro g hg
    obtain ⟨a, ha⟩ := scalarCenterHom_surjective hdeg hn ⟨g, hg⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · exact scalarSubgroup_le_center F K hdeg n

theorem card_center (hdeg : Module.finrank F K = 2) (hn : 0 < n) :
    Nat.card (Subgroup.center (SU F K n hdeg)) = Nat.gcd n (Nat.card F + 1) := by
  rw [← Nat.card_congr (scalarCenterEquiv hdeg hn).toEquiv]
  exact card_scalarParameters F K hdeg n

end Atlas.Unitary

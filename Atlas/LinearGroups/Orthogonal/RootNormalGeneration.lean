import Atlas.LinearGroups.Orthogonal.RootSubgroupConjugation
import Atlas.LinearGroups.Orthogonal.ElementaryPairStandard
import Mathlib.GroupTheory.Subgroup.Simple

/-! # Conjugates of one singular-line root subgroup generate the actual elementary group -/
noncomputable section
namespace Atlas.Orthogonal
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e : V) (he : Q e = 0)

theorem root_normalClosure_eq_top
    (ht : ∀ u : V, u ≠ 0 → Q u = 0 →
      ∃ g : isometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val e = u) :
    Subgroup.normalClosure
      (((rootSubgroup Q e he).subgroupOf (elementarySubgroup Q)) : Set (elementarySubgroup Q)) = ⊤ := by
  let A := (rootSubgroup Q e he).subgroupOf (elementarySubgroup Q)
  let N := Subgroup.normalClosure (A : Set (elementarySubgroup Q))
  have hle : elementarySubgroup Q ≤ N.map (elementarySubgroup Q).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨u, v, hu, huv, rfl⟩
    by_cases hun : u = 0
    · subst u
      have hid : siegelElement Q 0 v hu huv = 1 := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        change Atlas.Quadratic.siegel Q 0 v x = x
        simp [Atlas.Quadratic.siegel]
      rw [hid]
      exact Subgroup.one_mem _
    · obtain ⟨g, hg, hgu⟩ := ht u hun hu
      have hr : siegelElement Q u v hu huv ∈ rootSubgroup Q u hu :=
        ⟨Multiplicative.ofAdd ⟨v, huv⟩, rfl⟩
      have hr' : siegelElement Q u v hu huv ∈ (rootSubgroup Q e he).map (MulAut.conj g) := by
        rw [rootSubgroup_conj]
        simpa only [hgu] using hr
      obtain ⟨r, hr, hrg⟩ := hr'
      have hre : r ∈ elementarySubgroup Q := rootSubgroup_le_elementary Q e he hr
      have hrn : (⟨r, hre⟩ : elementarySubgroup Q) ∈ N :=
        Subgroup.subset_normalClosure hr
      refine ⟨(⟨g, hg⟩ : elementarySubgroup Q) * ⟨r, hre⟩ * ⟨g, hg⟩⁻¹,
        (inferInstance : N.Normal).conj_mem _ hrn _, ?_⟩
      exact hrg
  apply top_unique
  intro g _
  obtain ⟨z, hz, hzg⟩ := hle g.prop
  have heq : z = g := Subtype.ext hzg
  exact heq ▸ hz

theorem rootB_normalClosure_eq_top (n : ℕ) (h2 : (2 : F) ≠ 0)
    (e : VectorB (n+2) F) (he : formB (n+2) F e = 0) (hne : e ≠ 0) :
    Subgroup.normalClosure
      (((rootSubgroup (formB (n+2) F) e he).subgroupOf (elementarySubgroup (formB (n+2) F))) :
        Set (elementarySubgroup (formB (n+2) F))) = ⊤ :=
  root_normalClosure_eq_top _ e he (fun u hu hqu =>
    elementaryB_singular_transport n h2 e u hne hu he hqu)
end Atlas.Orthogonal

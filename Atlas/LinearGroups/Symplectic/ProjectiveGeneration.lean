import Atlas.LinearGroups.Symplectic.Generation
import Atlas.LinearGroups.Symplectic.Projective

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

def projectiveTransvectionGroup (n : ℕ) (F : Type*) [Field F] : Subgroup (PSp n F) :=
  Subgroup.closure {g | ∃ (v : Vector n F) (a : F), g = projection (transvection v a)}

theorem projectiveTransvectionGroup_eq_top : projectiveTransvectionGroup n F = ⊤ := by
  have hle : transvectionGroup n F ≤ (projectiveTransvectionGroup n F).comap projection := by
    apply (Subgroup.closure_le _).mpr
    rintro t ⟨v,a,rfl⟩
    exact Subgroup.subset_closure ⟨v,a,rfl⟩
  apply top_unique
  intro p _
  obtain ⟨g,rfl⟩ := projection_surjective p
  exact hle (mem_transvectionGroup n g)

/-- Projective transitivity comes from genuine transvections, without an order argument. -/
theorem exists_projective_send (p q : Points n F) :
    ∃ g : PSp n F, g • p = q := by
  obtain ⟨g,_,hg⟩ := exists_generated_send p.rep_nonzero q.rep_nonzero
  refine ⟨projection g,?_⟩
  rw [projection_smul,← Projectivization.mk_rep p, Projectivization.smul_mk]
  simpa only [hg] using Projectivization.mk_rep q

instance projective_pretransitive : MulAction.IsPretransitive (PSp n F) (Points n F) :=
  ⟨exists_projective_send⟩

end Atlas.Symplectic

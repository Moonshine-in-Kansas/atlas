import Atlas.LinearGroups.ReeF4.SpecialElementaryPointReduction
import Atlas.LinearGroups.ReeF4.SpecialPoints

/-! Transitivity on the intrinsic projective special points, obtained from
explicit elementary reduction of representatives. No order is used. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem elementary_specialPoint_transitive {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (p q : SpecialPoints (F := F) m) :
    ∃ g : elementarySubgroup hcard, g.val • p = q := by
  obtain ⟨g, hg⟩ := elementary_specialVector_transitive hcard p.property q.property
  refine ⟨g, ?_⟩
  conv_lhs => rw [← specialPointMk_rep m p]
  rw [specialPointMk_smul]
  simpa only [hg] using specialPointMk_rep m q

theorem model_specialPoint_transitive {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    MulAction.IsPretransitive (Model F m) (SpecialPoints (F := F) m) where
  exists_smul_eq p q := by
    obtain ⟨g, hg⟩ := elementary_specialPoint_transitive hcard p q
    exact ⟨g.val, hg⟩

end Atlas.ReeF4

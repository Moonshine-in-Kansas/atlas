import Atlas.LinearGroups.Chevalley.Comparison.TypeDNaturalProjective
import Atlas.LinearGroups.Chevalley.ModelSimplicityGood

/-! Injectivity of the literal descended D natural map over finite fields.
Only the independently proved new Model simplicity and the marked nontrivial
image are used. No old-group simplicity or either group-order theorem is used. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeD

theorem modelNaturalProjectiveHom_injective (n : ℕ) (hn : 4≤n+2)
    (K : Type*) [Field K] [Finite K] :
    Function.Injective (modelNaturalProjectiveHom n hn K) := by
  letI : Fintype K := Fintype.ofFinite K
  have hgood : (RootType.D (n+2) hn).Good (Fintype.card K) :=
    ⟨Fintype.one_lt_card,trivial⟩
  letI : IsSimpleGroup (Model (.D (n+2) hn) K) :=
    model_isSimpleGroup_of_good (.D (n+2) hn) K hgood
  let f := modelNaturalProjectiveHom n hn K
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hbot | htop
  · exact f.ker_eq_bot_iff.mp hbot
  · have hx : modelX (.D (n+2) hn) K (0 : Fin (n+2)) 1 ∈ f.ker := by
      rw [htop]
      exact Subgroup.mem_top _
    exact False.elim (modelNaturalProjectiveHom_X_one_ne_one n hn K hx)

end Atlas.Chevalley.Comparison.TypeD

import Atlas.GroupTheory.PairStabilizer

noncomputable section
namespace Atlas.GroupTheory
open MulAction
open scoped Pointwise

/-- For a two-point set, moving one point proves surjectivity of restriction. -/
theorem pairRestriction_surjective_of_moves {G X : Type*} [Group G] [MulAction G X]
    (a b : X) (hab : a ≠ b)
    (hm : ∃ g : PairStabilizer (G := G) a b, g.val • a ≠ a) :
    Function.Surjective (pairRestrictionHom (G := G) a b) := by
  classical
  obtain ⟨g,hg⟩ := hm
  have ha : g.val • a = b := by
    rcases (pairStabilizer_mem a b hab g.val).mp g.prop with h | h
    · exact False.elim (hg h.1)
    · exact h.1
  have hb : g.val • b = a := by
    rcases (pairStabilizer_mem a b hab g.val).mp g.prop with h | h
    · exact False.elim (hg h.1)
    · exact h.2
  let aa : ({a,b} : Set X) := ⟨a,Or.inl rfl⟩
  let bb : ({a,b} : Set X) := ⟨b,Or.inr rfl⟩
  have hne : aa ≠ bb := fun h => hab (congrArg Subtype.val h)
  intro σ
  have hinj := σ.injective.ne hne
  rcases (σ aa).prop with h | h
  · have hσa : σ aa = aa := Subtype.ext h
    have hσb : σ bb = bb := by
      rcases (σ bb).prop with hh | hh
      · exact False.elim (hinj (hσa.trans (Subtype.ext hh).symm))
      · exact Subtype.ext hh
    refine ⟨1,Equiv.ext ?_⟩
    intro y
    rcases y.prop with hy | hy
    · have hy' : y = aa := Subtype.ext hy
      simpa only [hy',map_one,Equiv.Perm.one_apply] using hσa.symm
    · have hy' : y = bb := Subtype.ext hy
      simpa only [hy',map_one,Equiv.Perm.one_apply] using hσb.symm
  · have hσa : σ aa = bb := Subtype.ext h
    have hσb : σ bb = aa := by
      rcases (σ bb).prop with hh | hh
      · exact Subtype.ext hh
      · exact False.elim (hinj (hσa.trans (show σ bb = bb from Subtype.ext hh).symm))
    refine ⟨g,Equiv.ext ?_⟩
    intro y
    rcases y.prop with hy | hy
    · have hy' : y = aa := Subtype.ext hy
      rw [hy',hσa]
      exact Subtype.ext ha
    · have hy' : y = bb := Subtype.ext hy
      rw [hy',hσb]
      exact Subtype.ext hb

end Atlas.GroupTheory

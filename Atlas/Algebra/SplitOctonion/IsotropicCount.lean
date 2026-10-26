import Atlas.Algebra.SplitOctonion.NormCounts

namespace Atlas.SplitOctonion
variable {F : Type*} [Field F] [Finite F]

abbrev NonzeroIsotropic (F : Type*) [Field F] :=
  {x : {v : Carrier F // norm v=0} // x.val≠0}

theorem card_nonzero_isotropic :
    Nat.card (NonzeroIsotropic F) = (Nat.card F ^ 4 - 1) * (Nat.card F ^ 3 + 1) := by
  classical
  letI := Fintype.ofFinite F
  letI : Unique {x : {v : Carrier F // norm v=0} // x.val=0} :=
    { default := ⟨⟨0,by simp [norm]⟩,rfl⟩
      uniq := fun x => Subtype.ext (Subtype.ext x.prop) }
  have hz : Fintype.card {x : {v : Carrier F // norm v=0} // x.val=0} = 1 :=
    Fintype.card_unique
  change Nat.card {x : {v : Carrier F // norm v=0} // x.val≠0} = _
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,hz,
    ←Nat.card_eq_fintype_card,card_norm_zero,_root_.mul_add,_root_.mul_one]
  have h : 1 ≤ Nat.card F ^ 4 := one_le_pow₀ (by
    have := Finite.one_lt_card (α:=F)
    omega)
  omega

end Atlas.SplitOctonion

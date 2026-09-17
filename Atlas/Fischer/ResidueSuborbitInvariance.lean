import Atlas.Fischer.ResidueSuborbitPartition

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes MulAction

theorem residueSuborbitIndex_invariant (S : Finset Omega) (i : Omega) (hi : i ∉ S)
    (g : stabilizer (ResidueGroup S) (residueBasicPoint S i hi)) (x : ResiduePoint S) :
    residueSuborbitIndex S i hi (g • x)=residueSuborbitIndex S i hi x := by
  classical
  have heq : g • x=residueBasicPoint S i hi ↔ x=residueBasicPoint S i hi := by
    constructor
    · intro h
      exact smul_left_cancel g.val (h.trans g.property.symm)
    · rintro rfl
      exact g.property
  obtain ⟨a,ha⟩ := QuotientGroup.mk_surjective g.val
  have hf : (MulAut.conj a.val) (distinguishedRootElement (.inl i))=
      distinguishedRootElement (.inl i) := by
    have h := g.property
    rw [← ha] at h
    exact congrArg Subtype.val h
  have hc : Commute (distinguishedRootElement (.inl i)) (g • x).val ↔
      Commute (distinguishedRootElement (.inl i)) x.val := by
    have h := commute_map_iff (MulAut.conj a.val).injective
      (x := distinguishedRootElement (.inl i)) (y := x.val)
    rw [hf] at h
    change Commute (distinguishedRootElement (.inl i)) (g.val • x).val ↔ _
    rw [← ha]
    exact h
  simp only [residueSuborbitIndex,heq,hc]

end Atlas.Fischer

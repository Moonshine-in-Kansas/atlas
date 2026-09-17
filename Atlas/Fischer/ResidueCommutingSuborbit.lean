import Atlas.Fischer.ResidueSuborbitPartition

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes MulAction

theorem residueAppendedCentralizer_le (S : Finset Omega) (i : Omega) :
    residueCentralizer (insert i S) ≤ residueCentralizer S := by
  intro g hg
  rintro x ⟨j,hj,rfl⟩
  exact hg _ ⟨j,Finset.mem_insert_of_mem hj,rfl⟩

def residueAppendedStabilizerHom (S : Finset Omega) (i : Omega) (hi : i ∉ S) :
    residueCentralizer (insert i S) →*
      stabilizer (ResidueGroup S) (residueBasicPoint S i hi) :=
  ((QuotientGroup.mk' (residueCentralElementary S)).comp
    (Subgroup.inclusion (residueAppendedCentralizer_le S i))).codRestrict _ (by
      intro g
      apply Subtype.ext
      change g.val * distinguishedRootElement (.inl i) * g.val⁻¹=
        distinguishedRootElement (.inl i)
      exact (mem_markedPentadPointwise_iff (insert i S) g.val).mp g.property i
        (Finset.mem_insert_self _ _))

/-- The full commuting suborbit is transitive by appended-clique homogeneity. -/
theorem residueCommutingSuborbit_transitive (S : Finset Omega) (hS : S.card ≤ 3)
    (i : Omega) (hi : i ∉ S) (x y : ResiduePoint S)
    (hx : residueSuborbitIndex S i hi x=1) (hy : residueSuborbitIndex S i hi y=1) :
    ∃ g : stabilizer (ResidueGroup S) (residueBasicPoint S i hi), g • x=y := by
  classical
  have hSi : (insert i S).card ≤ 4 := by rw [Finset.card_insert_of_notMem hi]; omega
  letI := residuePoint_transitive (insert i S) hSi
  let X := residueCommutingFiberEquiv S i hi ⟨x,hx⟩
  let Y := residueCommutingFiberEquiv S i hi ⟨y,hy⟩
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (residueCentralizer (insert i S)) X Y
  refine ⟨residueAppendedStabilizerHom S i hi g,?_⟩
  apply Subtype.ext
  have hz := congrArg (fun z : ResiduePoint (insert i S) => z.val) hg
  change g.val*x.val*g.val⁻¹=y.val at hz ⊢
  exact hz

end Atlas.Fischer

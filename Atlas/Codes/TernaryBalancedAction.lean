import Atlas.Codes.TernaryBalancedHexads
import Atlas.Codes.TernaryTriadFlags

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Codes

def ternaryBalancedPermutation (g : TernaryPureAutomorphism) (c : TernaryBalancedWords) :
    TernaryBalancedWords :=
  ⟨⟨fun i => c.val.val (g.val.symm i),g.prop c.val.val c.val.prop⟩,
    ternaryBalanced_permute g.val c.val.val c.prop⟩

theorem ternarySupport_permute (g : Equiv.Perm (Fin 12)) (c : TernaryWord) :
    ternarySupport (fun i => c (g.symm i))=(ternarySupport c).map g.toEmbedding := by
  ext i
  simp [ternarySupport,Finset.mem_map_equiv]

theorem ternaryBalanced_positive_flags_transitive (c d : TernaryBalancedWords)
    (i j : Fin 12) (hi : c.val.val i=1) (hj : d.val.val j=1) :
    ∃ g : TernaryPureAutomorphism,
      (∀ k,c.val.val (g.val.symm k)=d.val.val k) ∧ g.val i=j := by
  have hci : i ∈ ternaryPositiveSupport c.val.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
  have hdj : j ∈ ternaryPositiveSupport d.val.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
  obtain ⟨g,hg,hij⟩ := ternaryTriadFlags_transitive _ _ c.prop.1 d.prop.1 i j hci hdj
  have he : (ternaryBalancedPermutation g c).val=d.val :=
    ternaryBalanced_positive_unique _ _ (ternaryBalancedPermutation g c).prop d.prop (by
      change ternaryPositiveSupport (fun k => c.val.val (g.val.symm k))=ternaryPositiveSupport d.val.val
      rw [ternaryPositiveSupport_permute,hg])
  exact ⟨g,fun k => congrArg (fun w : ternaryGolay => w.val k) he,hij⟩

end Atlas.Codes

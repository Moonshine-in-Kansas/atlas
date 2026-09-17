import Atlas.Codes.TernaryBalancedOutsideData

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Codes

def ternaryBalancedBaseCode : TernaryBalancedWords :=
  ⟨ternaryGolayEquiv ![1,1,1,0,0,0],by decide +kernel⟩

theorem ternaryBalancedBaseCode_val : ternaryBalancedBaseCode.val.val=ternaryBalancedBase := by
  decide +kernel

theorem ternaryBalanced_toBase (c : TernaryBalancedWords) :
    ∃ g : TernaryPureAutomorphism,∀ i,c.val.val (g.val.symm i)=ternaryBalancedBase i := by
  obtain ⟨g,hg⟩ := ternaryTriads_transitive (ternaryPositiveSupport c.val.val)
    (ternaryPositiveSupport ternaryBalancedBaseCode.val.val) c.prop.1 ternaryBalancedBaseCode.prop.1
  have he : (ternaryBalancedPermutation g c).val=ternaryBalancedBaseCode.val :=
    ternaryBalanced_positive_unique _ _ (ternaryBalancedPermutation g c).prop
      ternaryBalancedBaseCode.prop (by
        change ternaryPositiveSupport (fun i => c.val.val (g.val.symm i))=_
        rw [ternaryPositiveSupport_permute,hg])
  exact ⟨g,fun i => (congrArg (fun w : ternaryGolay => w.val i) he).trans
    (congrFun ternaryBalancedBaseCode_val i)⟩

theorem ternaryBalanced_outside_toBase (c : TernaryBalancedWords) (j : Fin 12)
    (hj : j ∉ ternarySupport c.val.val) :
    ∃ g : TernaryPureAutomorphism,
      (∀ i,c.val.val (g.val.symm i)=ternaryBalancedBase i) ∧ g.val j=3 := by
  obtain ⟨g,hg⟩ := ternaryBalanced_toBase c
  have hx : g.val j ∉ ternarySupport ternaryBalancedBase := by
    have hz : c.val.val j=0 := by simpa [ternarySupport] using hj
    have he := hg (g.val j)
    simp only [Equiv.symm_apply_apply,hz] at he
    simp [ternarySupport,← he]
  obtain ⟨a,ha⟩ := ternaryBalancedOutsidePermutation_transitive (g.val j) hx
  let h := ternaryBalancedOutsideAutomorphism a
  refine ⟨h⁻¹*g,?_,?_⟩
  · intro i
    change c.val.val (g.val.symm (h.val i))=ternaryBalancedBase i
    rw [hg]
    have hh := congrFun (ternaryBalancedOutsidePermutation_fixed a) (h.val i)
    simpa [h,ternaryBalancedOutsideAutomorphism] using hh.symm
  · change h.val.symm (g.val j)=3
    exact h.val.symm_apply_eq.mpr ha.symm

/-- The actual M11 is transitive on balanced signed hexads with a marked outside point. -/
theorem ternaryBalanced_outside_flags_transitive (c d : TernaryBalancedWords)
    (i j : Fin 12) (hi : i ∉ ternarySupport c.val.val) (hj : j ∉ ternarySupport d.val.val) :
    ∃ g : TernaryPureAutomorphism,
      (∀ k,c.val.val (g.val.symm k)=d.val.val k) ∧ g.val i=j := by
  obtain ⟨g,hg,hi⟩ := ternaryBalanced_outside_toBase c i hi
  obtain ⟨h,hh,hj⟩ := ternaryBalanced_outside_toBase d j hj
  refine ⟨h⁻¹*g,?_,?_⟩
  · intro k
    change c.val.val (g.val.symm (h.val k))=d.val.val k
    rw [hg]
    simpa using (hh (h.val k)).symm
  · change h.val.symm (g.val i)=j
    rw [hi,← hj,Equiv.symm_apply_apply]

end Atlas.Codes

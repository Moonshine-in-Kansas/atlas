import Atlas.Rudvalis.HeavySelectedRowWeights
import Atlas.Rudvalis.CoupleMonomialGenerators

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

noncomputable def codeRowImage (g : codeGroup) (p : Point) : Point :=
  binaryBlockPermutation (codePermutationHom g) p

theorem codeRowImage_coordinates (g : codeGroup) (z : Coordinate) :
    (g.val.right z).1=codeRowImage g z.1 :=
  binaryBlockPermutation_coordinates (codePermutationHom g) z

noncomputable def codeInnerEquiv (g : codeGroup) (p : Point) : Equiv.Perm E :=
  Equiv.ofBijective (fun x => (g.val.right (p,x)).2) (by
    have hi : Function.Injective (fun x : E => (g.val.right (p,x)).2) := by
      intro x y h
      have hh : g.val.right (p,x)=g.val.right (p,y) :=
        Prod.ext ((codeRowImage_coordinates g (p,x)).trans (codeRowImage_coordinates g (p,y)).symm) h
      exact congrArg Prod.snd (g.val.right.injective hh)
    exact ⟨hi,Finite.surjective_of_injective hi⟩)

theorem codeInnerEquiv_coordinates (g : codeGroup) (p : Point) (x : E) :
    g.val.right (p,x)=(codeRowImage g p,codeInnerEquiv g p x) :=
  Prod.ext (codeRowImage_coordinates g _) rfl

theorem codeAction_row_weight (g : codeGroup) (w : QuaternaryWord) (p : Point) :
    hammingNorm (fun x => reduce (monomialHom g.val w) (codeRowImage g p,x))=
      hammingNorm (fun x => reduce w (p,x)) := by
  classical
  have he (x : E) : reduce (monomialHom g.val w) (codeRowImage g p,codeInnerEquiv g p x)=reduce w (p,x) := by
    rw [←codeInnerEquiv_coordinates]
    change reduce (monomialAction g.val w) (g.val.right (p,x))=_
    rw [monomialAction_reduce]
    exact congrArg (reduce w) (g.val.right.symm_apply_apply _)
  simp only [Atlas.Codes.hammingNorm_eq_sum]
  rw [←Equiv.sum_comp (codeInnerEquiv g p)]
  simp only [he]

theorem heavyWord_action_exists (g : codeGroup) (w : HeavyMinimumWords) :
    ∃u : HeavyMinimumWords,monomialHom g.val w.val.val=u.val.val := by
  let u : MinimumWords := g • heavyMinimumWord w
  have hu : hasNonzeroQuadraticPart (reduce u.val.val) := by
    rcases quaternary_minimum_support_cases u.val.val u.val.prop u.prop with h|h
    · have hc := codeAction_activeBlocks_card g w.val.val
      change (activeBlocks (reduce u.val.val)).card=(activeBlocks (reduce w.val.val)).card at hc
      rw [heavy_activeBlocks_card _ w.prop.2,four_minimum_activeBlocks_card _ u.val.prop u.prop h] at hc
      omega
    · exact h
  exact ⟨⟨u.val,u.prop,hu⟩,rfl⟩

/-- The quadratic heavy label is exactly the unique row of residue weight four. -/
theorem heavyWord_label_transport (g : codeGroup) (v w : HeavyMinimumWords)
    (c d : Point) (a : FixedHeavyParameters c) (b : FixedHeavyParameters d)
    (hv : reduce v.val.val=fixedHeavyWord c a) (hw : reduce w.val.val=fixedHeavyWord d b)
    (h : monomialHom g.val v.val.val=w.val.val) : codeRowImage g c=d := by
  have hc := codeAction_row_weight g v.val.val c
  rw [h,hv,hw,fixedHeavyWord_row_weight,fixedHeavyWord_row_weight,ite_eq_left rfl] at hc
  by_contra hn
  rw [ite_eq_right hn] at hc
  omega

theorem coupleCodeBeta_rowImage (r : Fin 7) :
    codeRowImage coupleCodeBeta (rowLabel r)=rowLabel (coupleBetaRow r) := by
  have h := coupleCodeBeta_row r 0
  rw [codeRowImage_coordinates] at h
  exact h

end Atlas.Rudvalis

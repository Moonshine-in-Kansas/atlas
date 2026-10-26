import Atlas.Rudvalis.SignCrossPhase
import Atlas.Rudvalis.HeavySelectedRowWeights

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem code_sign_fix_full_rows (g : codeGroup) (hg : g.val.right=1)
    (v : MinimalShell) (hrows : ∀p : Point,∃x : E,v.val.val (p,x)≠0)
    (hv : g • v=v) : g=1 := by
  have hs := code_sign_patterns g hg
  have hzero (p : Point) : g.val.left.toAdd (p,0)=0 := by
    obtain ⟨x,hx⟩ := hrows p
    have he := congrArg (fun w : MinimalShell => w.val.val (p,x)) hv
    change liftedSign (g.val.left.toAdd (p,x)) (v.val.val (g.val.right.symm (p,x)))=v.val.val (p,x) at he
    rw [hg] at he
    change liftedSign (g.val.left.toAdd (p,x)) (v.val.val (p,x))=v.val.val (p,x) at he
    rw [signPatterns_block_constant _ hs p x] at he
    by_contra h
    simp only [liftedSign,h,ite_false] at he
    exact hx (by linarith)
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change g.val.left.toAdd=0
    funext i
    exact (signPatterns_block_constant _ hs i.1 i.2).trans (hzero i.1)
  · exact hg

theorem heavyMinimumWord_nonzero_each_row (w : HeavyMinimumWords) (p : Point) :
    ∃x : E,(minimumWordShellLift (heavyMinimumWord w)).val.val (p,x)≠0 := by
  classical
  let d := (⟨⟨reduce w.val.val,(quaternaryCode_residue _).mpr ⟨w.val.val,w.val.prop,rfl⟩⟩,
    w.prop.2,quaternary_minimum_residue_weight _ w.val.prop w.prop.1⟩ : HeavyMinimumResidues)
  let a := quadraticMinimumWordEquiv.symm d
  have hr : fixedHeavyWord a.1 a.2=reduce w.val.val :=
    congrArg (fun z : HeavyMinimumResidues => z.val.val) (quadraticMinimumWordEquiv.apply_symm_apply d)
  have hh := fixedHeavyWord_row_weight a.1 p a.2
  have hp : 0<hammingNorm (fun x => fixedHeavyWord a.1 a.2 (p,x)) := by
    rw [hh]; split_ifs <;> omega
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hp
  have hn := (Finset.mem_filter.mp hx).2
  refine ⟨x,?_⟩
  intro hz
  have he := (minimumWordShellLift_zero_iff (heavyMinimumWord w) (p,x)).mp hz
  change reduce w.val.val (p,x)=0 at he
  exact hn (by rw [hr];exact he)

theorem code_sign_heavy_cross_scalar (g : codeGroup) (hg : g.val.right=1)
    (w : HeavyMinimumWords)
    (hw : g • minimalCross (minimumWordShellLift (heavyMinimumWord w))=
      minimalCross (minimumWordShellLift (heavyMinimumWord w))) :
    g=1 ∨ g=codeI^2 := by
  let v := minimumWordShellLift (heavyMinimumWord w)
  have hrows := heavyMinimumWord_nonzero_each_row w
  rcases code_sign_cross_phase g hg v hw with hv|hv
  · exact Or.inl (code_sign_fix_full_rows g hg v hrows hv)
  · have hp : (codeI^2).val.right=1 := by
      change (codeI.val*codeI.val).right=1
      rw [codeI_squared_signed]
      rfl
    have hk : (codeI^2*g).val.right=1 := by
      change (codeI^2).val.right*g.val.right=1
      rw [hp,hg,one_mul]
    have hf : (codeI^2*g) • v=v := by
      rw [mul_smul,hv,←mul_smul,←pow_add]
      norm_num only [Nat.reduceAdd]
      rw [codeI_pow_four,one_smul]
    have he := code_sign_fix_full_rows (codeI^2*g) hk v hrows hf
    right
    have hi : (codeI^2)*(codeI^2)=1 := by rw [←pow_add]; exact codeI_pow_four
    calc
      g=1*g := (one_mul g).symm
      _=(codeI^2*codeI^2)*g := by rw [hi]
      _=codeI^2*(codeI^2*g) := mul_assoc _ _ _
      _=codeI^2 := by rw [he,mul_one]
end Atlas.Rudvalis

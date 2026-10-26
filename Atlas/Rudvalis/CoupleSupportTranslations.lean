import Atlas.Rudvalis.CoupleFourStateAction
import Atlas.Rudvalis.FourLocalSupports

namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary

/-- Equal affine-plane parity permits a translation fixing the entire reference row. -/
theorem four_support_pair_fixed_translation (a p₀ r s : Point)
    (hr : dot a.val r.val=1) (hs : dot a.val s.val=1)
    (hrs : r.val+s.val=p₀.val) (ε δ : Point→Bit)
    (hε : ∀p,dot a.val p.val=0 → ε p=0)
    (hδ : ∀p,dot a.val p.val=0 → δ p=0)
    (hpar : (∑p,ε p)=(∑p,δ p)) (hpair : ε r+ε s=δ r+δ s) :
    ∃B : BinaryMatrix,matrixAt B p₀.val=0 ∧
      binaryNormalMap (δ,outerMatrix a.val a.val,0)=
      binaryNormalMap (ε,outerMatrix a.val a.val,0) ∘ coordinateTranslation B := by
  have hz : ∀p,dot a.val p.val=0 → (δ+ε) p=0 := by
    intro p hp; simp [hε p hp,hδ p hp]
  have he : (∑p,(δ+ε) p)=0 := by
    simp only [Pi.add_apply,Finset.sum_add_distrib,hpar,CharTwo.add_self_eq_zero]
  obtain ⟨u,hu⟩ := even_active_linear_restriction a (δ+ε) hz he
  have hp : dot u p₀.val=0 := by
    rw [←hrs,dot_add_right,←hu r hr,←hu s hs]
    change (δ r+ε r)+(δ s+ε s)=0
    calc _=(δ r+δ s)+(ε r+ε s) := by ring
         _=0 := by rw [hpair,CharTwo.add_self_eq_zero]
  obtain ⟨i,hi⟩ := point_has_one a
  let z := (basisPoint i).val
  have haz : dot a.val z=1 := by rw [dot_comm,dot_basisPoint]; exact hi
  refine ⟨outerMatrix z u,?_,?_⟩
  · rw [matrixAt_outer,hp,zero_smul]
  · funext q
    rcases q with ⟨p,x⟩
    change δ p+dot (matrixAt (outerMatrix a.val a.val) p.val) x+theta p 0 x=
      ε p+dot (matrixAt (outerMatrix a.val a.val) p.val) (x+matrixAt (outerMatrix z u) p.val)+
        theta p 0 (x+matrixAt (outerMatrix z u) p.val)
    simp only [theta_zero_parameter,add_zero,matrixAt_outer,dot_smul_left,dot_add_right,dot_smul_right,haz,mul_one]
    rcases Atlas.Codes.bit_cases (dot a.val p.val) with hp|hp
    · simp [hp,hε p hp,hδ p hp]
    · have hd := hu p hp
      change δ p+ε p=dot u p.val at hd
      rw [hp,one_mul,mul_one,←hd]
      have hh : ∀a b c : Bit,a+c=b+(c+(a+b)) := by decide +kernel
      exact hh _ _ _

theorem coupleFour_equal_parity_translation (a : Fin 3) (m n : E)
    (he : coupleFourParity a m=coupleFourParity a n) :
    ∃B : BinaryMatrix,matrixAt B (rowLabel 0).val=0 ∧
      coupleFourSupport a n=coupleFourSupport a m ∘ coordinateTranslation B := by
  let aa : Point := ⟨coupleFourForm a,coupleFourForm_ne_zero a⟩
  let r := rowLabel (![1,5,1] a)
  let s := rowLabel (![3,4,3] a)
  have hd : dot (coupleFourForm a) r.val=1 ∧ dot (coupleFourForm a) s.val=1 ∧
      r.val+s.val=(rowLabel 0).val := by
    dsimp [r,s]
    decide +kernel +revert
  have hm := coupleFourConstants_valid a m
  have hn := coupleFourConstants_valid a n
  apply four_support_pair_fixed_translation aa (rowLabel 0) r s hd.1 hd.2.1 hd.2.2
    (coupleFourConstants a m) (coupleFourConstants a n) hm.1 hn.1 (hm.2.trans hn.2.symm)
  simpa only [r,s,coupleFourConstants_rows,coupleFourParity] using he

end Atlas.Rudvalis

import Atlas.Rudvalis.FourSupportCount

/-! Translations connect the eight odd active-constant choices for each nonzero form. -/
namespace Atlas.Rudvalis
open scoped BigOperators

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem even_active_linear_restriction (a : Point) (f : Point → Bit)
    (hzero : ∀ p,dot a.val p.val=0 → f p=0) (hsum : (∑ p,f p)=0) :
    ∃ u : E,∀ p,dot a.val p.val=1 → f p=dot u p.val := by
  have hc : ∀ a : Fin 7,∀ f : Fin 7 → Bit,
      (∀ p,dot (rowLabel a).val (rowLabel p).val=0 → f p=0) → (∑ p,f p)=0 →
      ∃ u : Fin 8,∀ p,dot (rowLabel a).val (rowLabel p).val=1 → f p=dot (binaryLabel u) (rowLabel p).val := by
    decide +kernel
  obtain ⟨j,rfl⟩ := rowLabel_bijective.2 a
  have hz (i : Fin 7) := hzero (rowLabel i)
  have hs : (∑ i : Fin 7,f (rowLabel i))=0 := (Equiv.sum_comp rowEquiv f).trans hsum
  obtain ⟨u,hu⟩ := hc j (fun i => f (rowLabel i)) hz hs
  refine ⟨binaryLabel u,?_⟩
  intro p hp
  obtain ⟨i,rfl⟩ := rowLabel_bijective.2 p
  exact hu i hp

theorem four_support_fixed_form_translation (a : Point) (ε δ : Point → Bit)
    (hε : ∀ p,dot a.val p.val=0 → ε p=0)
    (hδ : ∀ p,dot a.val p.val=0 → δ p=0)
    (hs : (∑ p,ε p)=(∑ p,δ p)) :
    ∃ B : BinaryMatrix,binaryNormalMap (δ,outerMatrix a.val a.val,0)=
      binaryNormalMap (ε,outerMatrix a.val a.val,0) ∘ coordinateTranslation B := by
  have hz : ∀ p,dot a.val p.val=0 → (δ+ε) p=0 := by intro p hp; simp [hε p hp,hδ p hp]
  have he : (∑ p,(δ+ε) p)=0 := by simp only [Pi.add_apply,Finset.sum_add_distrib,hs,CharTwo.add_self_eq_zero]
  obtain ⟨u,hu⟩ := even_active_linear_restriction a (δ+ε) hz he
  obtain ⟨i,hi⟩ := point_has_one a
  let z := (basisPoint i).val
  have haz : dot a.val z=1 := by rw [dot_comm,dot_basisPoint]; exact hi
  refine ⟨outerMatrix z u,?_⟩
  funext q
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
    have hh : ∀ a b c : Bit,a+c=b+(c+(a+b)) := by decide +kernel
    exact hh _ _ _

end Atlas.Rudvalis

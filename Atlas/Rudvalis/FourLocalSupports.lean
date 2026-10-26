import Atlas.Rudvalis.FourLocalFibre
import Atlas.Rudvalis.FourSupportTranslations

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators
set_option maxRecDepth 16384

noncomputable def fourLocalConstants (m : ℕ) (p : Point) : Bit :=
  if dot (binaryLabel 1) p.val=1 then (m / 2^(rowEquiv.symm p).val : ℕ) else 0

theorem fourLocalConstants_rows (m : ℕ) (r : Fin 7) :
    fourLocalConstants m (rowLabel r)=
      if dot (binaryLabel 1) (rowLabel r).val=1 then ((m / 2^r.val : ℕ) : Bit) else 0 := by
  unfold fourLocalConstants
  change (if dot (binaryLabel 1) (rowLabel r).val=1 then ((m/2^(rowEquiv.symm (rowEquiv r)).val : ℕ) : Bit) else 0)=_
  rw [rowEquiv.symm_apply_apply]

noncomputable def fourLocalBaseConstants (b : Bool) : Point → Bit := fourLocalConstants (if b then 64 else 70)

theorem fourLocalBaseConstants_data (b : Bool) :
    (∀p,dot (binaryLabel 1) p.val=0 → fourLocalBaseConstants b p=0) ∧
    (∑p,fourLocalBaseConstants b p)=1 ∧
    fourLocalBaseConstants b (rowLabel 1)+fourLocalBaseConstants b (rowLabel 3)=(if b then 0 else 1) := by
  constructor
  · intro p hp
    simp [fourLocalBaseConstants,fourLocalConstants,hp]
  · rw [←Equiv.sum_comp rowEquiv]
    change (∑i,fourLocalConstants (if b then 64 else 70) (rowLabel i))=1 ∧ _
    simp only [fourLocalBaseConstants,fourLocalConstants_rows]
    decide +kernel +revert

/-- The point-fixing translations have two support orbits; Z joins their representatives. -/
theorem fourLocalConstants_translation (δ : Point → Bit)
    (hδ : ∀p,dot (binaryLabel 1) p.val=0 → δ p=0) (hs : (∑p,δ p)=1) :
    ∃b : Bool,∃B : BinaryMatrix,matrixAt B (rowLabel 0).val=0 ∧
      binaryNormalMap (δ,outerMatrix (binaryLabel 1) (binaryLabel 1),0)=
      binaryNormalMap (fourLocalBaseConstants b,outerMatrix (binaryLabel 1) (binaryLabel 1),0) ∘ coordinateTranslation B := by
  let b : Bool := decide (δ (rowLabel 1)+δ (rowLabel 3)=0)
  let ε := fourLocalBaseConstants b
  have he : (∀p,dot (binaryLabel 1) p.val=0 → ε p=0) ∧ (∑p,ε p)=1 ∧ ε (rowLabel 1)+ε (rowLabel 3)=(if b then 0 else 1) := fourLocalBaseConstants_data b
  have heq : δ (rowLabel 1)+δ (rowLabel 3)=ε (rowLabel 1)+ε (rowLabel 3) := by
    rw [he.2.2]
    have hb : ∀a : Bit,a=(if decide (a=0) then 0 else 1) := by decide +kernel
    exact hb _
  have hz : ∀p,dot (binaryLabel 1) p.val=0 → (δ+ε) p=0 := by
    intro p hp
    simp [hδ p hp,he.1 p hp]
  have hsum : (∑p,(δ+ε) p)=0 := by
    simp only [Pi.add_apply,Finset.sum_add_distrib,hs,he.2.1]
    decide +kernel
  let a : Point := ⟨binaryLabel 1,by decide +kernel⟩
  obtain ⟨u,hu⟩ := even_active_linear_restriction a (δ+ε) hz hsum
  have h1 := hu (rowLabel 1) (by decide +kernel)
  have h3 := hu (rowLabel 3) (by decide +kernel)
  have hp : dot u (rowLabel 0).val=0 := by
    rw [show (rowLabel 0).val=(rowLabel 1).val+(rowLabel 3).val from by decide +kernel,dot_add_right,←h1,←h3]
    change (δ (rowLabel 1)+ε (rowLabel 1))+(δ (rowLabel 3)+ε (rowLabel 3))=0
    calc _=(δ (rowLabel 1)+δ (rowLabel 3))+(ε (rowLabel 1)+ε (rowLabel 3)) := by ring
         _=0 := by rw [heq,CharTwo.add_self_eq_zero]
  let B := outerMatrix (binaryLabel 1) u
  refine ⟨b,B,?_,?_⟩
  · rw [matrixAt_outer,hp,zero_smul]
  · funext q
    rcases q with ⟨p,x⟩
    change δ p+dot (matrixAt (outerMatrix (binaryLabel 1) (binaryLabel 1)) p.val) x+theta p 0 x=
      ε p+dot (matrixAt (outerMatrix (binaryLabel 1) (binaryLabel 1)) p.val) (x+matrixAt B p.val)+theta p 0 (x+matrixAt B p.val)
    have haa : dot (binaryLabel 1) (binaryLabel 1)=1 := by decide +kernel
    simp only [B,theta_zero_parameter,add_zero,matrixAt_outer,dot_smul_left,dot_add_right,dot_smul_right,haa,mul_one]
    rcases Atlas.Codes.bit_cases (dot (binaryLabel 1) p.val) with h|h
    · simp [h,hδ p h,he.1 p h]
    · have hd := hu p h
      change δ p+ε p=dot u p.val at hd
      rw [h,one_mul,mul_one,←hd]
      have hh : ∀a b c : Bit,a+c=b+(c+(a+b)) := by decide +kernel
      exact hh _ _ _

end Atlas.Rudvalis

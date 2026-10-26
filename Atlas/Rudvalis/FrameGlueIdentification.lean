import Atlas.Rudvalis.FrameGlueBinary

/-! Identification of the literal three-block code with puncturing and shortening. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def frameGlueRestriction : BinaryWord →ₗ[Bit] FrameGlueWord where
  toFun w z := w (frameGluePoint z.1,z.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def frameGlueExtension : FrameGlueWord →ₗ[Bit] BinaryWord where
  toFun w z := ∑ i : Fin 3,if z.1=frameGluePoint i then w (i,z.2) else 0
  map_add' v w := by
    funext z
    dsimp
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split <;> simp

  map_smul' a w := by ext z; simp [mul_ite,Finset.mul_sum]

theorem frameGluePoint_injective : Function.Injective frameGluePoint := by decide +kernel

theorem frameGlueRestrictionExtension (w : FrameGlueWord) :
    frameGlueRestriction (frameGlueExtension w)=w := by
  funext z
  change (∑ i : Fin 3,if frameGluePoint z.1=frameGluePoint i then w (i,z.2) else 0)=w z
  simp only [frameGluePoint_injective.eq_iff]
  simp

theorem frameGlue_pairing_adjoint (v : BinaryWord) (w : FrameGlueWord) :
    Atlas.Codes.binaryDot v (frameGlueExtension w)=
      Atlas.Codes.binaryDot (frameGlueRestriction v) w := by
  classical
  change (∑ z : Coordinate,v z*(∑ i : Fin 3,if z.1=frameGluePoint i then w (i,z.2) else 0))=
    ∑ z : FrameGlueCoordinate,v (frameGluePoint z.1,z.2)*w z
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type,mul_ite,mul_zero]
  have hs (i : Fin 3) :
      (∑ p : Point,∑ x : E,if p=frameGluePoint i then v (p,x)*w (i,x) else 0)=
      ∑ x : E,v (frameGluePoint i,x)*w (i,x) := by
    rw [Finset.sum_comm]
    simp
  simp_rw [hs]

theorem frameGlueRestriction_normal (a : BinaryParameters) :
    frameGlueRestriction (binaryNormalMap a)=frameGlueNormalMap
      (fun i => a.1 (frameGluePoint i),
        ![matrixAt a.2.1 (frameGluePoint 0).val,matrixAt a.2.1 (frameGluePoint 1).val],a.2.2) := by
  funext z
  rcases z with ⟨i,x⟩
  fin_cases i
  · rfl
  · rfl
  · have hp : (frameGluePoint 2).val=(frameGluePoint 0).val+(frameGluePoint 1).val := by decide +kernel
    change a.1 (frameGluePoint 2)+dot (matrixAt a.2.1 (frameGluePoint 2).val) x+theta (frameGluePoint 2) a.2.2 x=
      a.1 (frameGluePoint 2)+dot (matrixAt a.2.1 (frameGluePoint 0).val+matrixAt a.2.1 (frameGluePoint 1).val) x+
        theta (frameGluePoint 2) a.2.2 x
    rw [hp,matrixAt_add_vector]

def frameGlueLiftParameters (a : FrameGlueParameters) : BinaryParameters :=
  ((fun p => if p=frameGluePoint 0 then a.1 0 else if p=frameGluePoint 1 then a.1 1
    else if p=frameGluePoint 2 then a.1 2 else 0),
    (fun j i => ![a.2.1 0 j,0,a.2.1 0 j+a.2.1 1 j] i),a.2.2)

theorem frameGlueLiftParameters_linear (a : FrameGlueParameters) (i : Fin 3) :
    matrixAt (frameGlueLiftParameters a).2.1 (frameGluePoint i).val=frameGlueLinear a.2.1 i := by
  ext j
  fin_cases i <;> simp [frameGlueLiftParameters,matrixAt,frameGluePoint,binaryLabel,frameGlueLinear,Fin.sum_univ_succ]
  exact CharTwo.add_cancel_left _ _

theorem frameGlueLiftParameters_constant (a : FrameGlueParameters) (i : Fin 3) :
    (frameGlueLiftParameters a).1 (frameGluePoint i)=a.1 i := by
  fin_cases i <;> simp [frameGlueLiftParameters,frameGluePoint_injective.eq_iff]

theorem frameGlueRestriction_lift (a : FrameGlueParameters) :
    frameGlueRestriction (binaryNormalMap (frameGlueLiftParameters a))=frameGlueNormalMap a := by
  funext z
  rcases z with ⟨i,x⟩
  change (frameGlueLiftParameters a).1 (frameGluePoint i)+
    dot (matrixAt (frameGlueLiftParameters a).2.1 (frameGluePoint i).val) x+theta (frameGluePoint i) a.2.2 x=_
  rw [frameGlueLiftParameters_constant,frameGlueLiftParameters_linear]
  rfl

theorem frameGlueCode_puncturing : binaryResidue.map frameGlueRestriction=frameGlueCode := by
  ext w
  constructor
  · rintro ⟨v,⟨a,rfl⟩,rfl⟩
    rw [frameGlueRestriction_normal]
    exact ⟨_,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨binaryNormalMap (frameGlueLiftParameters a),⟨_,rfl⟩,frameGlueRestriction_lift a⟩

theorem frameGlueCode_shortening (w : FrameGlueWord) :
    frameGlueExtension w∈binaryTorsion ↔ w∈frameGlueCode := by
  rw [← frameGlueCode_self_dual]
  constructor
  · intro hw v hv
    obtain ⟨d,hd,rfl⟩ := (frameGlueCode_puncturing.symm ▸ hv)
    rw [← frameGlue_pairing_adjoint]
    exact hw d hd
  · intro hw d hd
    rw [frameGlue_pairing_adjoint]
    apply hw
    rw [← frameGlueCode_puncturing]
    exact Submodule.mem_map_of_mem hd

end Atlas.Rudvalis

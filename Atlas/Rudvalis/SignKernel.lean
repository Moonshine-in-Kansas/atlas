import Atlas.Rudvalis.SignGram
import Atlas.Rudvalis.HammingSignCode

/-! The full sign-pattern code is the four-dimensional Hamming code. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def rowSigns (a : Point → Bit) : BinaryWord := fun z => a z.1

theorem rowSigns_generator_pair (a : Point → Bit) (i j : Fin 19) :
    Atlas.Codes.binaryDot (signGenerator i) (fun z => rowSigns a z*signGenerator j z)=
      dot (generatorGramVector i j) (rowMoment a) := by
  rw [Atlas.Codes.binaryDot_apply,Fintype.sum_prod_type]
  calc
    _ = ∑ p : Point, a p*generatorBlockGram i j p := by
      apply Finset.sum_congr rfl
      intro p _
      rw [generatorBlockGram,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [rowSigns]
      ring
    _ = ∑ p : Point, a p*dot (generatorGramVector i j) p.val := by
      simp_rw [generatorBlockGram_linear]
    _ = dot (generatorGramVector i j) (rowMoment a) := by
      simp only [dot,rowMoment,LinearMap.coe_mk,AddHom.coe_mk,Finset.sum_apply,
        Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem rowSigns_mem_iff (a : Point → Bit) : rowSigns a∈signPatterns ↔ rowMoment a=0 := by
  constructor
  · intro ha
    ext k
    have hi : signGenerator ⟨7+k.val,by omega⟩∈binaryResidue := ⟨_,rfl⟩
    have hj : signGenerator 16∈binaryResidue := ⟨_,rfl⟩
    have h := ha (signGenerator 16) hj (signGenerator ⟨7+k.val,by omega⟩) hi
    rw [Atlas.Codes.binaryDot_apply,Fintype.sum_prod_type] at h
    have he : (∑ p : Point, ∑ x : E, signGenerator ⟨7+k.val,by omega⟩ (p,x)*
        (rowSigns a (p,x)*signGenerator 16 (p,x))) = ∑ p : Point,a p*p.val k := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← generatorBlockGram_coordinate k p]
      simp only [generatorBlockGram,Finset.mul_sum,rowSigns]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [he] at h
    exact h
  · intro ha
    intro d hd e he
    obtain ⟨b,rfl⟩ := hd
    obtain ⟨c,rfl⟩ := he
    rw [binaryNormalMap_expansion b,binaryNormalMap_expansion c]
    simp only [Atlas.Codes.binaryDot_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    obtain ⟨v,rfl⟩ := seedGeneratorIndex_surjective i
    obtain ⟨u,rfl⟩ := seedGeneratorIndex_surjective j
    have h := rowSigns_generator_pair a u v
    rw [ha] at h
    have hz : dot (generatorGramVector u v) 0=0 := by simp [dot]
    rw [hz] at h
    have hh : (∑ z : Coordinate,
        binaryParameterCoefficient c (seedGeneratorIndex u)*
          binaryNormalMap (binaryParameterGenerator (seedGeneratorIndex u)) z*
          (rowSigns a z*(binaryParameterCoefficient b (seedGeneratorIndex v)*
            binaryNormalMap (binaryParameterGenerator (seedGeneratorIndex v)) z))) =
        binaryParameterCoefficient c (seedGeneratorIndex u)*binaryParameterCoefficient b (seedGeneratorIndex v)*
          Atlas.Codes.binaryDot (signGenerator u) (fun z=>rowSigns a z*signGenerator v z) := by
      rw [Atlas.Codes.binaryDot_apply,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      simp only [signGenerator]
      ring
    rw [hh,h,mul_zero]

noncomputable def hammingSignEquiv : hammingSignCode ≃ₗ[Bit] signPatterns where
  toFun a := ⟨rowSigns a.val,(rowSigns_mem_iff _).mpr a.prop⟩
  invFun s := ⟨(fun p => s.val (p,0)),by
    change rowMoment (fun p => s.val (p,0))=0
    apply (rowSigns_mem_iff _).mp
    have h : rowSigns (fun p => s.val (p,0))=s.val := by
      funext z
      exact (signPatterns_block_constant s.val s.prop z.1 z.2).symm
    rw [h]
    exact s.prop⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv s := by
    apply Subtype.ext
    funext z
    exact (signPatterns_block_constant s.val s.prop z.1 z.2).symm
  map_add' a b := by apply Subtype.ext; rfl
  map_smul' a b := by apply Subtype.ext; rfl

theorem signPatterns_card : Nat.card signPatterns=16 := by
  rw [← Nat.card_congr hammingSignEquiv.toEquiv,hammingSignCode_card]

theorem signPatterns_finrank : Module.finrank Bit signPatterns=4 := by
  rw [← hammingSignEquiv.finrank_eq,hammingSignCode_finrank]

end Atlas.Rudvalis


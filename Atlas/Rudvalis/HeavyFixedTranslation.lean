import Atlas.Rudvalis.HeavyTranslationImage
import Atlas.Rudvalis.BinaryBlocks

/-! Fixed-radical heavy supports form one orbit under actual coordinate translations. -/
namespace Atlas.Rudvalis

theorem blockWeight_two_unique (a b : Bit) (u c : E)
    (ha : blockWeight a u c=2) (hb : blockWeight b u c=2) : a=b := by
  decide +kernel +revert

theorem quadratic_minimum_constants_off (ε δ : Point→Bit) (M : BinaryMatrix) (c : E)
    (hc : c≠0) (hε : hammingNorm (binaryNormalMap (ε,M,c))=16)
    (hδ : hammingNorm (binaryNormalMap (δ,M,c))=16) (p : Point) (hp : p.val≠c) : ε p=δ p := by
  have he := (binaryNormalMap_quadratic_weight_sixteen (ε,M,c) hc).mp hε p
  have hd := (binaryNormalMap_quadratic_weight_sixteen (δ,M,c) hc).mp hδ p
  simp only [if_neg hp] at he hd
  exact blockWeight_two_unique _ _ _ _ he hd

theorem translatedParameters_heavy_flip (ε : Point→Bit) (M : BinaryMatrix) (c u : E)
    (hm : matrixAt M.transpose c=0) (hu : dot u c=1) :
    translatedParameters (outerMatrix c u) (ε,M,c)=
      ((fun p => ε p+(if p.val=c then 1 else 0)),M,c) := by
  apply Prod.ext
  · funext p
    rw [translatedParameters_heavy_constant ε M c u hm p,hu]
  · change (M+crossMatrix c*outerMatrix c u,c)=(M,c)
    rw [crossMatrix_outer_zero,add_zero]

theorem quadratic_minimum_same_matrix_translation (ε δ : Point→Bit) (M : BinaryMatrix) (c : E)
    (hc : c≠0) (hε : hammingNorm (binaryNormalMap (ε,M,c))=16)
    (hδ : hammingNorm (binaryNormalMap (δ,M,c))=16) :
    ∃ A : BinaryMatrix,binaryNormalMap (δ,M,c)=binaryNormalMap (ε,M,c) ∘ coordinateTranslation A := by
  let p : Point := ⟨c,hc⟩
  have hoff := quadratic_minimum_constants_off ε δ M c hc hε hδ
  by_cases he : ε p=δ p
  · have hεδε : ε=δ := by
      funext q
      by_cases hq : q.val=c
      · have hqp : q=p := Subtype.ext hq
        simpa [hqp] using he
      · exact hoff q hq
    refine ⟨0,?_⟩
    rw [hεδε]
    funext z
    change binaryNormalMap (δ,M,c) z=binaryNormalMap (δ,M,c) (z.1,z.2+matrixAt 0 z.1.val)
    have hz : matrixAt (0 : BinaryMatrix) z.1.val=0 := by ext i; simp [matrixAt]
    rw [hz,add_zero]
  · obtain ⟨i,hi⟩ := point_has_one p
    let u : E := Pi.single i 1
    have hu : dot u c=1 := by simpa [u,dot,Pi.single_apply,ite_mul] using hi
    have hm := binaryNormalMap_quadratic_minimum_contraction (ε,M,c) hc hε
    have hd : (fun q : Point => ε q+(if q.val=c then 1 else 0))=δ := by
      funext q
      by_cases hq : q.val=c
      · have hqp : q=p := Subtype.ext hq
        rw [if_pos hq,hqp]
        have hb : ∀ a b : Bit,a≠b → a+1=b := by decide +kernel
        exact hb _ _ he
      · rw [if_neg hq,add_zero,hoff q hq]
    refine ⟨outerMatrix c u,?_⟩
    rw [←binaryNormalMap_translation,translatedParameters_heavy_flip ε M c u hm hu,hd]

theorem quadratic_minimum_fixed_radical_translation (ε δ : Point→Bit) (M N : BinaryMatrix) (c : E)
    (hc : c≠0) (hε : hammingNorm (binaryNormalMap (ε,M,c))=16)
    (hδ : hammingNorm (binaryNormalMap (δ,N,c))=16) :
    ∃ A : BinaryMatrix,binaryNormalMap (δ,N,c)=binaryNormalMap (ε,M,c) ∘ coordinateTranslation A := by
  have hM := binaryNormalMap_quadratic_minimum_contraction (ε,M,c) hc hε
  have hN := binaryNormalMap_quadratic_minimum_contraction (δ,N,c) hc hδ
  have hd : matrixAt (N-M).transpose c=0 := by
    change transposeContraction c (N-M)=0
    rw [map_sub]
    change matrixAt N.transpose c-matrixAt M.transpose c=0
    rw [hM,hN,sub_self]
  obtain ⟨A,hA⟩ := crossMatrix_image c hc (N-M) hd
  let γ := (translatedParameters A (ε,M,c)).1
  have ht : translatedParameters A (ε,M,c)=(γ,N,c) := by
    apply Prod.ext
    · rfl
    change (M+crossMatrix c*A,c)=(N,c)
    rw [hA]
    congr 1
    abel
  have hw : hammingNorm (binaryNormalMap (γ,N,c))=16 := by
    rw [←ht,binaryNormalMap_translation,binaryWord_weight_permute,hε]
  obtain ⟨B,hB⟩ := quadratic_minimum_same_matrix_translation γ δ N c hc hw hδ
  refine ⟨A+B,?_⟩
  rw [hB,←ht,binaryNormalMap_translation,coordinateTranslation_mul]
  rfl

end Atlas.Rudvalis

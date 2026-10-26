import Atlas.Rudvalis.FanoLinear
import Atlas.Rudvalis.BlockAffine

/-! Affine coordinate maps in the intrinsic seven blocks. -/
namespace Atlas.Rudvalis

noncomputable def blockCoordinateEquiv (g : binaryPermutationGroup) (p : Point) : Equiv.Perm E where
  toFun x := (g.val (p,x)).2
  invFun y := ((g.val⁻¹ : Equiv.Perm Coordinate) (binaryBlockHom g p,y)).2
  left_inv x := by
    have he : (binaryBlockHom g p,(g.val (p,x)).2)=g.val (p,x) :=
      Prod.ext (binaryBlockPermutation_coordinates g (p,x)).symm rfl
    simp [he]
  right_inv y := by
    let z := (g.val⁻¹ : Equiv.Perm Coordinate) (binaryBlockHom g p,y)
    have hz : g.val z=(binaryBlockHom g p,y) := by simp [z]
    have hp : z.1=p := (binaryBlockHom g).injective
      ((binaryBlockPermutation_coordinates g z).symm.trans (congrArg Prod.fst hz))
    change (g.val (p,z.2)).2=y
    rw [← hp]
    exact congrArg Prod.snd hz

theorem blockCoordinateEquiv_coordinates (g : binaryPermutationGroup) (p : Point) (x : E) :
    g.val (p,x)=(binaryBlockHom g p,blockCoordinateEquiv g p x) :=
  Prod.ext (binaryBlockPermutation_coordinates g (p,x)) rfl

theorem affine_fourActive_restriction (p : Point) (a : Bit) (b : E) (hb : b≠0) :
    ∃ w : BinaryWord, w∈binaryResidue ∧ hammingNorm w=16 ∧
      (activeBlocks w).card=4 ∧ ∀ x : E, w (p,x)=a+dot b x := by
  obtain ⟨i,hi⟩ := point_has_one p
  let u := basisPoint i
  have hu : dot u.val p.val=1 := by rw [dot_basisPoint]; exact hi
  let M := outerMatrix b u.val
  let ε : Point → Bit := fun q => if q=p then a else 0
  have hr : isBinaryRankOne M := ⟨⟨b,hb⟩,u,rfl⟩
  have hn := ((isBinaryRankOne_iff M).mp hr).1
  have hz (q : Point) (hq : matrixAt M q.val=0) : ε q=0 := by
    by_cases hqp : q=p
    · subst q
      have he : matrixAt M p.val=b := by simp [M,matrixAt_outer,hu]
      exact False.elim (hb (he.symm.trans hq))
    · simp [ε,hqp]
  have hw : hammingNorm (binaryNormalMap (ε,M,0))=16 :=
    (binaryNormalMap_bilinear_weight_sixteen ε M hn).mpr ⟨hr,hz⟩
  refine ⟨binaryNormalMap (ε,M,0),⟨_,rfl⟩,hw, ?_, ?_⟩
  · rw [activeBlocks_bilinear_minimum _ _ hn hw]
    exact ((isBinaryRankOne_iff M).mp hr).2
  · intro x
    change ε p + dot (matrixAt M p.val) x + theta p 0 x = a+dot b x
    have hm : matrixAt M p.val=b := by simp only [M,matrixAt_outer,hu,one_smul]
    rw [hm]
    simp [ε,theta,eta,quadratic,dot]


theorem blockCoordinateEquiv_affine_function (g : binaryPermutationGroup) (p : Point)
    (a : Bit) (b : E) : ∃ d : Bit, ∃ e : E,
      ∀ x, a+dot b (blockCoordinateEquiv g p x)=d+dot e x := by
  by_cases hb : b=0
  · exact ⟨a,0,by simp [hb,dot]⟩
  obtain ⟨w,hw,hweight,hactive,hres⟩ := affine_fourActive_restriction (binaryBlockHom g p) a b hb
  have hm : w ∘ g.val ∈ binaryResidue := (g.prop w).mp hw
  obtain ⟨d,hd⟩ := hm
  have hc : w ∘ (((g⁻¹).val)⁻¹ : Equiv.Perm Coordinate)=w ∘ g.val := by simp
  have hca : (activeBlocks (binaryNormalMap d)).card=4 := by
    rw [hd,← hc,activeBlocks_permute,
      Finset.card_image_of_injective _ (binaryBlockHom (g⁻¹)).injective]
    exact hactive
  have hcw : hammingNorm (binaryNormalMap d)=16 := by
    rw [hd,binaryWord_weight_permute,hweight]
  have hzero := (fourActive_parameters d hcw hca).1
  refine ⟨d.1 p,matrixAt d.2.1 p.val, ?_⟩
  intro x
  calc
    a+dot b (blockCoordinateEquiv g p x) =
        w (binaryBlockHom g p,blockCoordinateEquiv g p x) := (hres _).symm
    _ = w (g.val (p,x)) := congrArg w (blockCoordinateEquiv_coordinates g p x).symm
    _ = binaryNormalMap d (p,x) := (congrFun hd (p,x)).symm
    _ = d.1 p + dot (matrixAt d.2.1 p.val) x := by
      change d.1 p + dot (matrixAt d.2.1 p.val) x + theta p d.2.2 x = _
      simp [hzero,theta,eta,quadratic,dot]


theorem blockCoordinateEquiv_preserves_affine (g : binaryPermutationGroup) (p : Point)
    (f : E → Bit) (hf : IsAffineFunction f) :
    IsAffineFunction (f ∘ blockCoordinateEquiv g p) := by
  obtain ⟨a,b,hf⟩ := hf
  obtain ⟨d,e,he⟩ := blockCoordinateEquiv_affine_function g p a b
  exact ⟨d,e,fun x => (hf _).trans (he x)⟩

theorem binaryPermutation_block_affine (g : binaryPermutationGroup) (p : Point) :
    ∃ A : BinaryMatrix, ∃ t : E, IsUnit A ∧
      ∀ x, (g.val (p,x)).2=matrixAt A x+t :=
  affine_code_permutation (blockCoordinateEquiv g p) (blockCoordinateEquiv_preserves_affine g p)

end Atlas.Rudvalis



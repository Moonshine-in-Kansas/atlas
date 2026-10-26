import Atlas.Rudvalis.MinimumStrata
import Atlas.Rudvalis.BinaryBlocks

/-! Intrinsic Fano geometry reconstructed from the four-block words. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def activeBlocks (w : BinaryWord) : Finset Point :=
  Finset.univ.filter (fun p => hammingNorm (fun x : E => w (p,x)) ≠ 0)

set_option maxHeartbeats 1000000 in
theorem binaryNormalMap_row_weight (a : BinaryParameters) (p : Point) :
    hammingNorm (fun x : E => binaryNormalMap a (p,x)) =
      blockWeight (a.1 p) (matrixAt a.2.1 p.val + eta p a.2.2) a.2.2 := by
  unfold blockWeight
  congr 1
  funext x
  change a.1 p + dot (matrixAt a.2.1 p.val) x + theta p a.2.2 x =
    a.1 p + dot (matrixAt a.2.1 p.val + eta p a.2.2) x + quadratic a.2.2 x
  rw [dot_add_left]
  unfold theta
  ring

theorem activeBlocks_quadratic (a : BinaryParameters) (hc : a.2.2 ≠ 0) :
    activeBlocks (binaryNormalMap a) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro p
  simp only [activeBlocks,Finset.mem_filter,Finset.mem_univ,true_and,binaryNormalMap_row_weight]
  have := blockWeight_quadratic_lower (a.1 p) (matrixAt a.2.1 p.val + eta p a.2.2) a.2.2 hc
  omega

theorem activeBlocks_constant (ε : Point → Bit) :
    (activeBlocks (binaryNormalMap (ε,0,0))).card = hammingNorm ε := by
  simp only [activeBlocks,binaryNormalMap_row_weight]
  have he (p : Point) : matrixAt (0 : BinaryMatrix) p.val + eta p 0 = 0 := by
    ext j
    simp [matrixAt,eta]
  simp only [he,blockWeight_affine,ite_true]
  simp [hammingNorm]

theorem fourActive_parameters (a : BinaryParameters)
    (hw : hammingNorm (binaryNormalMap a) = 16)
    (ha : (activeBlocks (binaryNormalMap a)).card = 4) : a.2.2=0 ∧ a.2.1≠0 := by
  have hc : a.2.2=0 := by
    by_contra hn
    rw [activeBlocks_quadratic a hn] at ha
    norm_num at ha
  refine ⟨hc, ?_⟩
  intro hM
  have he : a = (a.1,0,0) := Prod.ext rfl (Prod.ext hM hc)
  rw [he,activeBlocks_constant] at ha
  rw [he,binaryNormalMap_constant_weight,ha] at hw
  omega

theorem activeBlocks_bilinear_minimum (ε : Point → Bit) (M : BinaryMatrix)
    (hM : M≠0) (hw : hammingNorm (binaryNormalMap (ε,M,0))=16) :
    activeBlocks (binaryNormalMap (ε,M,0)) = nonzeroMatrixBlocks M := by
  have hc := ((binaryNormalMap_bilinear_weight_sixteen ε M hM).mp hw).2
  ext p
  simp only [activeBlocks,nonzeroMatrixBlocks,Finset.mem_filter,Finset.mem_univ,true_and,
    binaryNormalMap_row_weight]
  have he : eta p 0 = 0 := by simp [eta]
  simp only [he,add_zero,blockWeight_affine]
  by_cases hp : matrixAt M p.val=0
  · simp [hp,hc p hp]
  · simp [hp]

def IsFanoComplement (s : Finset Point) : Prop := ∃ u : Point, s = linearOnes u.val

theorem fourActive_fano (w : BinaryWord) (hw : w ∈ binaryResidue)
    (hweight : hammingNorm w=16) (hactive : (activeBlocks w).card=4) :
    IsFanoComplement (activeBlocks w) := by
  obtain ⟨a,rfl⟩ := hw
  obtain ⟨hc,hM⟩ := fourActive_parameters a hweight hactive
  have he : a = (a.1,a.2.1,0) := Prod.ext rfl (Prod.ext rfl hc)
  rw [he] at hweight ⊢
  obtain ⟨⟨b,u,hr⟩,_⟩ := (binaryNormalMap_bilinear_weight_sixteen _ _ hM).mp hweight
  refine ⟨u, ?_⟩
  rw [activeBlocks_bilinear_minimum _ _ hM hweight,hr,outerMatrix_active]


theorem fano_fourActive (s : Finset Point) (hs : IsFanoComplement s) :
    ∃ w : BinaryWord, w ∈ binaryResidue ∧ hammingNorm w=16 ∧
      (activeBlocks w).card=4 ∧ activeBlocks w=s := by
  obtain ⟨u,rfl⟩ := hs
  let M := outerMatrix (basisPoint 0).val u.val
  have hr : isBinaryRankOne M := ⟨basisPoint 0,u,rfl⟩
  have hn := ((isBinaryRankOne_iff M).mp hr).1
  have hw : hammingNorm (binaryNormalMap (0,M,0))=16 :=
    (binaryNormalMap_bilinear_weight_sixteen 0 M hn).mpr ⟨hr,fun _ _ => rfl⟩
  have ha : activeBlocks (binaryNormalMap (0,M,0))=linearOnes u.val := by
    rw [activeBlocks_bilinear_minimum _ _ hn hw]
    exact outerMatrix_active (basisPoint 0) u
  exact ⟨binaryNormalMap (0,M,0),⟨_,rfl⟩,hw,ha ▸ linear_ones_count u.val u.prop,ha⟩

theorem mem_activeBlocks (w : BinaryWord) (p : Point) :
    p ∈ activeBlocks w ↔ ∃ x : E, w (p,x) ≠ 0 := by
  simp only [activeBlocks,Finset.mem_filter,Finset.mem_univ,true_and,
    hammingNorm_ne_zero_iff,Function.ne_iff,Pi.zero_apply]

theorem activeBlocks_permute (g : binaryPermutationGroup) (w : BinaryWord) :
    activeBlocks (w ∘ (g.val⁻¹ : Equiv.Perm Coordinate)) =
      (activeBlocks w).image (binaryBlockHom g) := by
  ext p
  rw [mem_activeBlocks,Finset.mem_image]
  constructor
  · rintro ⟨x,hx⟩
    let z := (g.val⁻¹ : Equiv.Perm Coordinate) (p,x)
    have hz : (g.val z).1=p := by simp [z]
    refine ⟨z.1,(mem_activeBlocks w z.1).mpr ⟨z.2,hx⟩, ?_⟩
    exact (binaryBlockPermutation_coordinates g z).symm.trans hz
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨x,hx⟩ := (mem_activeBlocks w q).mp hq
    refine ⟨(g.val (q,x)).2, ?_⟩
    have he : (binaryBlockHom g q,(g.val (q,x)).2)=g.val (q,x) :=
      Prod.ext (binaryBlockPermutation_coordinates g (q,x)).symm rfl
    simpa [Function.comp_def,he] using hx

theorem binaryBlockHom_preserves_fano (g : binaryPermutationGroup) (s : Finset Point)
    (hs : IsFanoComplement s) : IsFanoComplement (s.image (binaryBlockHom g)) := by
  obtain ⟨w,hw,hweight,hcard,ha⟩ := fano_fourActive s hs
  have ht : w ∘ (g.val⁻¹ : Equiv.Perm Coordinate) ∈ binaryResidue :=
    ((g⁻¹).prop w).mp hw
  have hcard' : (activeBlocks (w ∘ (g.val⁻¹ : Equiv.Perm Coordinate))).card=4 := by
    rw [activeBlocks_permute,Finset.card_image_of_injective _ (binaryBlockHom g).injective]
    exact hcard
  have hf := fourActive_fano _ ht (by rw [binaryWord_weight_permute,hweight]) hcard'
  simpa only [activeBlocks_permute,ha] using hf

end Atlas.Rudvalis


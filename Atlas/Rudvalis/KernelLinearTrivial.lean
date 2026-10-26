import Atlas.Rudvalis.FanoBlockAffine
import Atlas.Rudvalis.AlternatingRadicals

namespace Atlas.Rudvalis
open scoped BigOperators

theorem blockFixed_row_weight (g : binaryPermutationGroup) (hg : binaryBlockHom g=1)
    (w : BinaryWord) (p : Point) :
    hammingNorm (fun x : E => (w ∘ g.val) (p,x)) = hammingNorm (fun x : E => w (p,x)) := by
  have he (x : E) : (w ∘ g.val) (p,x)=w (p,blockCoordinateEquiv g p x) := by
    rw [Function.comp_apply,blockCoordinateEquiv_coordinates,hg]
    rfl
  simp only [Atlas.Codes.hammingNorm_eq_sum,he]
  exact Equiv.sum_comp (blockCoordinateEquiv g p) (fun x => if w (p,x)=0 then 0 else 1)

theorem blockFixed_minimum_quadratic_class (g : binaryPermutationGroup)
    (hg : binaryBlockHom g=1) (a d : BinaryParameters) (ha : a.2.2≠0)
    (hw : hammingNorm (binaryNormalMap a)=16)
    (hd : binaryNormalMap d=binaryNormalMap a ∘ g.val) : d.2.2=a.2.2 := by
  have hrow (p : Point) :
      blockWeight (d.1 p) (matrixAt d.2.1 p.val+eta p d.2.2) d.2.2 =
      if p.val=a.2.2 then 4 else 2 := by
    rw [← binaryNormalMap_row_weight,hd,blockFixed_row_weight g hg,
      binaryNormalMap_row_weight]
    exact (binaryNormalMap_quadratic_weight_sixteen a ha).mp hw p
  have hdnonzero : d.2.2≠0 := by
    intro hd0
    have hex0 : ∀ c : E, ∃ p : Point, p.val≠c := by decide +kernel
    have hex := hex0 a.2.2
    obtain ⟨p,hp⟩ := hex
    have he := hrow p
    rw [if_neg hp,hd0,blockWeight_affine] at he
    split_ifs at he <;> omega
  have hdw : hammingNorm (binaryNormalMap d)=16 := by
    rw [hd,binaryWord_weight_permute,hw]
  have he := (binaryNormalMap_quadratic_weight_sixteen d hdnonzero).mp hdw ⟨a.2.2,ha⟩
  rw [hrow] at he
  simp only [ite_true] at he
  split_ifs at he with heq
  · exact heq.symm
  · omega

theorem quadratic_minimum_exists (c : E) (hc : c≠0) :
    ∃ a : BinaryParameters, a.2.2=c ∧ hammingNorm (binaryNormalMap a)=16 := by
  have hM : matrixAt (0 : BinaryMatrix).transpose c=0 := by ext i; simp [matrixAt]
  have hcard := quadraticConstants_count 0 c hc hM
  have hpos : 0 < Nat.card {ε : Point → Bit // hammingNorm (binaryNormalMap (ε,0,c))=16} := by omega
  obtain ⟨ε,hε⟩ := (Nat.card_pos_iff.mp hpos).1
  exact ⟨(ε,0,c),rfl,hε⟩

theorem affine_quadratic_second_difference (a : Bit) (b c t x y : E) :
    (a+dot b (x+y+t)+quadratic c (x+y+t))+
      (a+dot b (x+t)+quadratic c (x+t))+
      (a+dot b (y+t)+quadratic c (y+t))+
      (a+dot b t+quadratic c t)=polar c x y := by
  simp [dot,quadratic,polar,Fin.sum_univ_succ]
  ring_nf
  have htwo : (2 : Bit)=0 := by decide
  have hfour : (4 : Bit)=0 := by decide
  simp [htwo,hfour]

theorem blockFixed_common_linear_trivial (g : binaryPermutationGroup)
    (hg : binaryBlockHom g=1) (A : E ≃ₗ[Bit] E) (t : Point → E)
    (hcoord : ∀ p x, g.val (p,x)=(p,A x+t p)) : A=1 := by
  apply linearEquiv_preserving_polar_eq_one
  intro c x y
  by_cases hc : c=0
  · simp [hc,polar]
  · obtain ⟨a,ha,hw⟩ := quadratic_minimum_exists c hc
    obtain ⟨d,hd⟩ := (g.prop (binaryNormalMap a)).mp ⟨a,rfl⟩
    have hdclass : d.2.2=c := (blockFixed_minimum_quadratic_class g hg a d
      (ha.symm ▸ hc) hw hd).trans ha
    let p := basisPoint 0
    have he (z : E) :
        d.1 p+dot (matrixAt d.2.1 p.val+eta p c) z+quadratic c z =
        a.1 p+dot (matrixAt a.2.1 p.val+eta p c) (A z+t p)+quadratic c (A z+t p) := by
      have hz := congrFun hd (p,z)
      rw [Function.comp_apply,hcoord] at hz
      change d.1 p+dot (matrixAt d.2.1 p.val) z+theta p d.2.2 z =
        a.1 p+dot (matrixAt a.2.1 p.val) (A z+t p)+theta p a.2.2 (A z+t p) at hz
      rw [hdclass,ha] at hz
      calc
        _ = d.1 p+dot (matrixAt d.2.1 p.val) z+theta p c z := by
          rw [dot_add_left]; unfold theta; ring
        _ = _ := hz
        _ = _ := by rw [dot_add_left]; unfold theta; ring
    have hs := congrArg₂ (·+·) (congrArg₂ (·+·) (congrArg₂ (·+·)
      (he (x+y)) (he x)) (he y)) (he 0)
    simp only [map_add,map_zero,zero_add] at hs
    have hl := affine_quadratic_second_difference (d.1 p)
      (matrixAt d.2.1 p.val+eta p c) c 0 x y
    have hr := affine_quadratic_second_difference (a.1 p)
      (matrixAt a.2.1 p.val+eta p c) c (t p) (A x) (A y)
    simp only [add_zero] at hl
    exact (hl.symm.trans (hs.trans hr)).symm

end Atlas.Rudvalis

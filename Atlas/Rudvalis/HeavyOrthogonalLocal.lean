import Atlas.Rudvalis.HeavyFixedTranslation
import Atlas.Rudvalis.QuadraticWords

/-! The eight-point calculation for a heavy row and its Gaussian pairs. -/
namespace Atlas.Rudvalis
open scoped BigOperators

set_option maxHeartbeats 2000000 in
theorem quadratic_row_zero_pairs (a : Bit) (b c p : E) (hc : c≠0) (hp : p≠0)
    (hw : blockWeight a b c=if p=c then 4 else 2) :
    (Finset.univ.filter (fun x : E =>
      a+dot b x+quadratic c x=0 ∧ a+dot b (x+p)+quadratic c (x+p)=0)).card=
        if p=c then 0 else 4 := by
  decide +kernel +revert

abbrev FixedHeavyParameters (c : Point) := Σ M : (transposeContraction c.val).ker,
  {ε : Point→Bit // hammingNorm (binaryNormalMap (ε,M.val,c.val))=16}

theorem fixedHeavyParameters_card (c : Point) : Nat.card (FixedHeavyParameters c)=128 := by
  classical
  rw [Nat.card_sigma]
  have he (M : (transposeContraction c.val).ker) :
      Nat.card {ε : Point→Bit // hammingNorm (binaryNormalMap (ε,M.val,c.val))=16}=2 :=
    quadraticConstants_count M.val c.val c.prop (LinearMap.mem_ker.mp M.prop)
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,transposeContraction_ker_card c.val c.prop]

def fixedHeavyWord (c : Point) (v : FixedHeavyParameters c) : BinaryWord :=
  binaryNormalMap (v.2.val,v.1.val,c.val)

theorem fixedHeavy_row_pairs_card (c p : Point) (v : FixedHeavyParameters c) :
    (Finset.univ.filter (fun x : E => fixedHeavyWord c v (p,x)=0 ∧
      fixedHeavyWord c v (p,x+p.val)=0)).card=if p=c then 0 else 4 := by
  have hw := (binaryNormalMap_quadratic_weight_sixteen (v.2.val,v.1.val,c.val) c.prop).mp v.2.prop p
  have h := quadratic_row_zero_pairs (v.2.val p) (matrixAt v.1.val p.val+eta p c.val)
    c.val p.val c.prop p.prop hw
  have he (x : E) : fixedHeavyWord c v (p,x)=
      v.2.val p+dot (matrixAt v.1.val p.val+eta p c.val) x+quadratic c.val x := by
    change v.2.val p+dot (matrixAt v.1.val p.val) x+theta p c.val x=_
    simp only [theta,dot_add_left]
    ring
  simp_rw [he]
  simpa only [Subtype.val_inj] using h

end Atlas.Rudvalis

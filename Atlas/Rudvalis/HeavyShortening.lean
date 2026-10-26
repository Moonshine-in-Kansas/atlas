import Atlas.Rudvalis.HeavySeedGeometry
import Atlas.Codes.QuaternaryLiftFibres

/-! The actual heavy seed support has a four-dimensional shortened torsion code. -/
namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary

noncomputable def heavyShortCode := supportedCode binaryTorsion heavySeedResidue

noncomputable def heavyRowCoefficient (w : BinaryWord) (p : Point) : Bit :=
  let r := rowEquiv.symm p
  w (seedCoordinateEquiv (r,heavyRowRepresentative r))

theorem heavyRowCoefficient_apply (w : BinaryWord) (r : Fin 7) :
    heavyRowCoefficient w (rowLabel r)=w (seedCoordinateEquiv (r,heavyRowRepresentative r)) := by
  change w (seedCoordinateEquiv (rowEquiv.symm (rowEquiv r),heavyRowRepresentative (rowEquiv.symm (rowEquiv r))))=_
  simp

theorem torsion_seed_row_sum (w : BinaryWord) (hw : w∈binaryTorsion) (r : Fin 7) :
    (∑ k : Fin 8,w (seedCoordinateEquiv (r,k)))=0 := by
  have h := (Atlas.Codes.even_weight_iff _).mp (binaryTorsion_row_even w hw (rowLabel r))
  exact (Equiv.sum_comp (seedInnerEquiv r) (fun x => w (rowLabel r,x))).trans h

theorem torsion_seed_pairing (w : BinaryWord) (hw : w∈binaryTorsion)
    (v : BinaryWord) (hv : v∈binaryResidue) :
    (∑ r : Fin 7,∑ k : Fin 8,v (seedCoordinateEquiv (r,k))*w (seedCoordinateEquiv (r,k)))=0 := by
  have h := hw v hv
  rw [Atlas.Codes.binaryDot_apply,←Equiv.sum_comp seedCoordinateEquiv,Fintype.sum_prod_type] at h
  exact h

theorem heavyShort_row_constant (w : heavyShortCode) (r : Fin 7) (k : Fin 8) :
    w.val (seedCoordinateEquiv (r,k))=
      w.val (seedCoordinateEquiv (r,heavyRowRepresentative r))*heavySupportBit r k := by
  have hs (r : Fin 7) (k : Fin 8) (h : heavySupportBit r k=0) :
      w.val (seedCoordinateEquiv (r,k))=0 :=
    w.prop.2 _ ((heavySeedResidue_apply r k).trans h)
  have hp := torsion_seed_row_sum w.val w.prop.1
  have hn (r : Fin 7) (hr : r≠0) := heavySupport_nonheavy_row r hr
    (fun k => w.val (seedCoordinateEquiv (r,k))) (hs r) (hp r)
  by_cases hr : r=0
  · subst r
    apply heavySupport_heavy_row _ (hs 0) (hp 0) _ k
    intro i
    have h := torsion_seed_pairing w.val w.prop.1 (heavyMomentTest i) (heavyMomentTest_mem i)
    have he : (∑ r : Fin 7,∑ k : Fin 8,heavyMomentTest i (seedCoordinateEquiv (r,k))*
        w.val (seedCoordinateEquiv (r,k)))=
        ∑ k : Fin 8,heavyMomentRow i 0 k*w.val (seedCoordinateEquiv (0,k)) := by
      apply Finset.sum_eq_single 0
      · intro r _ hr
        have hc : (∑ k,heavyMomentTest i (seedCoordinateEquiv (r,k))*w.val (seedCoordinateEquiv (r,k)))=
            ∑ k,heavyMomentRow i r k*(w.val (seedCoordinateEquiv (r,heavyRowRepresentative r))*heavySupportBit r k) :=
          Finset.sum_congr rfl (fun k _ => congrArg (fun a => heavyMomentRow i r k*a) (hn r hr k))
        rw [hc]
        change (∑ k,heavyMomentRow i r k*(w.val (seedCoordinateEquiv (r,heavyRowRepresentative r))*heavySupportBit r k))=0
        have hh : (∑ k,heavyMomentRow i r k*(w.val (seedCoordinateEquiv (r,heavyRowRepresentative r))*heavySupportBit r k))=
            w.val (seedCoordinateEquiv (r,heavyRowRepresentative r))*(∑ k,heavyMomentRow i r k*heavySupportBit r k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        rw [hh,heavySupport_other_moment i r hr,mul_zero]
      · simp
    exact he.symm.trans h
  · exact hn r hr k

theorem heavyShort_block_constant (w : heavyShortCode) (z : Coordinate) :
    w.val z=heavyRowCoefficient w.val z.1*heavySeedResidue z := by
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective z
  rw [heavySeedResidue_apply]
  change w.val (seedCoordinateEquiv (r,k))=heavyRowCoefficient w.val (rowLabel r)*_
  rw [heavyRowCoefficient_apply]
  exact heavyShort_row_constant w r k

def heavyLinearTest (j : Fin 3) : BinaryWord := binaryNormalMap
  (0,outerMatrix (binaryLabel 2) (Pi.single j 1),0)

theorem heavyLinearTest_mem (j : Fin 3) : heavyLinearTest j∈binaryResidue := ⟨_,rfl⟩

theorem heavyLinearTest_row (j : Fin 3) (r : Fin 7) :
    (∑ k,heavyLinearTest j (rowLabel r,seedInnerLabel r k)*heavySupportBit r k)=(rowLabel r).val j := by
  decide +kernel +revert

theorem heavyShort_hamming (w : heavyShortCode) : heavyRowCoefficient w.val∈hammingSignCode := by
  change rowMoment (heavyRowCoefficient w.val)=0
  ext j
  change (∑ p : Point,heavyRowCoefficient w.val p • p.val) j=0
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply]
  rw [←Equiv.sum_comp rowEquiv]
  have h := torsion_seed_pairing w.val w.prop.1 (heavyLinearTest j) (heavyLinearTest_mem j)
  have he : (∑ r : Fin 7,∑ k : Fin 8,heavyLinearTest j (seedCoordinateEquiv (r,k))*
      w.val (seedCoordinateEquiv (r,k)))=
      ∑ r : Fin 7,heavyRowCoefficient w.val (rowEquiv r)*(rowEquiv r).val j := by
    apply Finset.sum_congr rfl
    intro r _
    calc
      _=∑ k : Fin 8,heavyLinearTest j (seedCoordinateEquiv (r,k))*
          (heavyRowCoefficient w.val (rowLabel r)*heavySupportBit r k) := by
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        rw [heavyShort_block_constant w,heavySeedResidue_apply]
        rfl
      _=heavyRowCoefficient w.val (rowLabel r)*
          (∑ k : Fin 8,heavyLinearTest j (seedCoordinateEquiv (r,k))*heavySupportBit r k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _=_ := by rw [show (∑ k : Fin 8,heavyLinearTest j (seedCoordinateEquiv (r,k))*heavySupportBit r k)=
          (rowLabel r).val j from heavyLinearTest_row j r]; rfl
  exact he.symm.trans h

noncomputable def heavyHammingRestriction (a : hammingSignCode) : heavyShortCode :=
  ⟨(fun z => rowSigns a.val z*heavySeedResidue z),
    ((rowSigns_mem_iff _).mpr a.prop) heavySeedResidue heavySeedResidue_mem,
    fun z hz => by simp [hz]⟩

noncomputable def heavyShortEquiv : heavyShortCode ≃ₗ[Bit] hammingSignCode where
  toFun w := ⟨heavyRowCoefficient w.val,heavyShort_hamming w⟩
  invFun := heavyHammingRestriction
  left_inv w := by
    apply Subtype.ext
    funext z
    exact (heavyShort_block_constant w z).symm
  right_inv a := by
    apply Subtype.ext
    funext p
    obtain ⟨r,rfl⟩ := rowEquiv.surjective p
    change heavyRowCoefficient (heavyHammingRestriction a).val (rowLabel r)=a.val (rowLabel r)
    rw [heavyRowCoefficient_apply]
    change a.val (rowLabel r)*heavySeedResidue (seedCoordinateEquiv (r,heavyRowRepresentative r))=a.val (rowLabel r)
    rw [heavySeedResidue_apply,heavySupport_representative,mul_one]
  map_add' w v := by apply Subtype.ext; rfl
  map_smul' a w := by apply Subtype.ext; rfl

theorem heavyShortCode_card : Nat.card heavyShortCode=16 := by
  rw [Nat.card_congr heavyShortEquiv.toEquiv,hammingSignCode_card]

theorem heavyShortCode_finrank : Module.finrank Bit heavyShortCode=4 := by
  rw [heavyShortEquiv.finrank_eq,hammingSignCode_finrank]

end Atlas.Rudvalis

import Atlas.Rudvalis.MinimumSupportClassification

/-! Seven nonzero forms, each with eight odd choices of active constants. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def activeConstants (a : Point) : Submodule Bit (Point → Bit) where
  carrier := {ε | ∀ p : Point,dot a.val p.val=0 → ε p=0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv p hp; simp [hu p hp,hv p hp]
  smul_mem' := by intro b u hu p hp; simp [hu p hp]

def activeConstantParity (a : Point) : activeConstants a →ₗ[Bit] Bit where
  toFun ε := ∑ p,ε.val p
  map_add' := by intro u v; simp [Finset.sum_add_distrib]
  map_smul' := by intro b u; simp [Finset.mul_sum]

noncomputable def activeParityOne (a : Point) : activeConstants a := by
  classical
  let i := (point_has_one a).choose
  have hi := (point_has_one a).choose_spec
  exact ⟨Pi.single (basisPoint i) 1,by
    intro p hp
    by_cases he : p=basisPoint i
    · subst p
      have hx : dot a.val (basisPoint i).val=1 := by
        rw [dot_comm,dot_basisPoint]
        exact hi
      exact False.elim (zero_ne_one (hp.symm.trans hx))
    · simp [he]⟩

theorem activeParityOne_parity (a : Point) : activeConstantParity a (activeParityOne a)=1 := by
  classical
  simp [activeParityOne,activeConstantParity]

abbrev OddActiveConstants (a : Point) := {ε : activeConstants a // activeConstantParity a ε=1}

noncomputable def activeParitySplit (a : Point) : activeConstants a ≃ Bit × OddActiveConstants a where
  toFun ε := (activeConstantParity a ε,
    ⟨ε+(1+activeConstantParity a ε) • activeParityOne a,by
      simp only [map_add,map_smul,smul_eq_mul,activeParityOne_parity,mul_one]
      rw [add_left_comm,CharTwo.add_self_eq_zero,add_zero]⟩)
  invFun v := v.2.val+(1+v.1) • activeParityOne a
  left_inv ε := by
    apply Subtype.ext
    funext p
    change ε.val p+(1+activeConstantParity a ε)*(activeParityOne a).val p+
      (1+activeConstantParity a ε)*(activeParityOne a).val p=ε.val p
    rw [add_assoc,CharTwo.add_self_eq_zero,add_zero]
  right_inv v := by
    rcases v with ⟨b,ε,hε⟩
    have hp : activeConstantParity a (ε+(1+b) • activeParityOne a)=b := by
      simp only [map_add,map_smul,smul_eq_mul,activeParityOne_parity,mul_one,hε]
      rw [← add_assoc,CharTwo.add_self_eq_zero,zero_add]
    apply Prod.ext hp
    apply Subtype.ext
    apply Subtype.ext
    funext p
    change ε.val p+(1+b)*(activeParityOne a).val p+
      (1+activeConstantParity a (ε+(1+b) • activeParityOne a))*(activeParityOne a).val p=ε.val p
    rw [hp,add_assoc,CharTwo.add_self_eq_zero,add_zero]

theorem activeConstants_card (a : Point) : Nat.card (activeConstants a)=16 := by
  have hr : isBinaryRankOne (outerMatrix a.val a.val) := ⟨a,a,rfl⟩
  have he : ∀ ε : Point → Bit, ε∈activeConstants a ↔
      hammingNorm (binaryNormalMap (ε,outerMatrix a.val a.val,0))=16 := by
    intro ε
    rw [binaryNormalMap_bilinear_weight_sixteen ε _ (outerMatrix_nonzero _ _ a.prop a.prop)]
    simp only [hr,true_and]
    change (∀ p,dot a.val p.val=0 → ε p=0) ↔ _
    simp only [matrixAt_outer,smul_eq_zero,a.prop,or_false]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact bilinearConstants_count _ hr

theorem oddActiveConstants_card (a : Point) : Nat.card (OddActiveConstants a)=8 := by
  have h := activeConstants_card a
  rw [Nat.card_congr (activeParitySplit a),Nat.card_prod] at h
  have hb : Nat.card Bit=2 := by simp [Bit]
  rw [hb] at h
  omega

abbrev FourSupportParameters := Σ a : Point,OddActiveConstants a

noncomputable def fourSupportEquiv : FourSupportParameters ≃ {d : BinaryWord // admissibleFourSupport d} :=
  Equiv.ofBijective (fun v =>
    ⟨binaryNormalMap (v.2.val.val,outerMatrix v.1.val v.1.val,0),
      v.1,v.2.val.val,rfl,v.2.val.prop,v.2.prop⟩) (by
    constructor
    · rintro ⟨a,ε⟩ ⟨b,δ⟩ h
      have he := binaryNormalMap_injective (congrArg Subtype.val h)
      have hm := congrArg (fun v : BinaryParameters => v.2.1) he
      have hab := congrArg Prod.fst (outerMatrix_nonzero_injective (a₁ := (a,a)) (a₂ := (b,b)) hm)
      change a=b at hab
      subst b
      have hε := congrArg Prod.fst he
      have hed : ε=δ := Subtype.ext (Subtype.ext hε)
      subst δ
      rfl
    · rintro ⟨d,a,ε,hd,hs,hp⟩
      refine ⟨⟨a,⟨⟨ε,hs⟩,hp⟩⟩,?_⟩
      exact Subtype.ext hd.symm)

theorem admissibleFourSupport_count : Nat.card {d : BinaryWord // admissibleFourSupport d}=56 := by
  classical
  rw [← Nat.card_congr fourSupportEquiv,Nat.card_sigma]
  simp only [oddActiveConstants_card,Finset.sum_const,Finset.card_univ,smul_eq_mul,card_Point]

end Atlas.Rudvalis

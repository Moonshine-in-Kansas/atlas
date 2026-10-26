import Atlas.LinearGroups.Orthogonal.Minus.RankTwoComparison
import Atlas.LinearGroups.Orthogonal.Minus.FullOrder
import Atlas.Algebra.FiniteFieldSignSquares
import Atlas.LinearGroups.Orthogonal.IntrinsicKernelIdentification

/-! The determinant/spinor quotient needs one represented hyperbolic plane, not two. -/
noncomputable section
namespace Atlas.Orthogonal
section Generic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)

theorem determinantSpinor_surjective_of_represents
    (hrep : ∀ c : F, c ≠ 0 → ∃ a : V, Q a = c) :
    Function.Surjective (determinantSpinor Q hQ h2) := by
  rintro ⟨c,s⟩
  obtain ⟨t,ht⟩ := specialSpinorNorm_surjective Q hQ h2 hrep s
  have htt : determinant Q t.val=1 := t.prop
  have hts : spinorNorm Q hQ h2 t.val=s := ht
  have hc : c.val.val^2=(1:F) := congrArg Units.val ((mem_rootsOfUnity 2 c.val).mp c.prop)
  rcases sq_eq_one_iff.mp hc with hc | hc
  · refine ⟨t.val,Prod.ext ?_ hts⟩
    apply Subtype.ext
    change determinant Q t.val=c.val
    rw [htt]
    exact Units.ext hc.symm
  · obtain ⟨a,ha⟩ := hrep 1 one_ne_zero
    have hane : Q a≠0 := ne_of_eq_of_ne ha one_ne_zero
    let r := reflectionElement Q a hane
    refine ⟨r*t.val,Prod.ext ?_ ?_⟩
    · apply Subtype.ext
      change determinant Q (r*t.val)=c.val
      rw [map_mul,htt,mul_one,reflectionElement_determinant]
      exact Units.ext hc.symm
    · change spinorNorm Q hQ h2 (r*t.val)=s
      rw [map_mul,spinorNorm_reflection]
      have he : Units.mk0 (Q a) hane=1 := Units.ext ha
      rw [he, map_one]
      change (1 : Atlas.SquareClass F) * spinorNorm Q hQ h2 t.val = s
      exact (_root_.one_mul _).trans hts

theorem determinantSpinor_kernel_index_of_represents [Finite F]
    (hrep : ∀ c : F, c≠0 → ∃ a : V, Q a=c) :
    (determinantSpinor Q hQ h2).ker.index=4 := by
  have he := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (determinantSpinor Q hQ h2)
    (determinantSpinor_surjective_of_represents Q hQ h2 hrep)).toEquiv
  change Nat.card (_ ⧸ (determinantSpinor Q hQ h2).ker)=4
  rw [he,Nat.card_prod,Atlas.card_squareOneUnits,Atlas.card_squareClass,ite_eq_right h2]
end Generic

namespace Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem rankTwo_represents (hdeg : Module.finrank F K = 2) (c : F) :
    ∃ v : Vector 1 F K, form hdeg 1 v=c := by
  refine ⟨(e 0+c • f 0,0),?_⟩
  simp [form_apply,formD_apply,e,f]

theorem rankTwo_determinantSpinor_surjective (hdeg : Module.finrank F K = 2)
    (h2 : (2 : F)≠0) :
    Function.Surjective (determinantSpinor (form hdeg 1) (polar_nondegenerate hdeg 1) h2) :=
  determinantSpinor_surjective_of_represents _ _ _ (fun c _ => rankTwo_represents hdeg c)

theorem rankTwo_determinantSpinor_kernel_index (hdeg : Module.finrank F K = 2)
    (h2 : (2 : F)≠0) :
    (determinantSpinor (form hdeg 1) (polar_nondegenerate hdeg 1) h2).ker.index=4 :=
  determinantSpinor_kernel_index_of_represents _ _ _ (fun c _ => rankTwo_represents hdeg c)

theorem rankTwo_elementary_le_intrinsic_kernel (hdeg : Module.finrank F K = 2)
    (h2 : (2 : F)≠0) :
    E hdeg 1 ≤ (determinantSpinor (form hdeg 1) (polar_nondegenerate hdeg 1) h2).ker := by
  rw [determinantSpinor_kernel]
  exact elementary_le_special_spinor _ _ _
theorem rankTwo_elementary_index_odd (hdeg : Module.finrank F K = 2)
    (h2 : (2 : F)≠0) : (E hdeg 1).index=4 := by
  let q := Nat.card F
  have hq : q%2=1 := Atlas.odd_card_mod_two h2
  have hp : 1≤q^2 := one_le_pow₀ Nat.card_pos
  have hm : (q^2-1)%2=0 := by
    have h : q^2%2=1 := by simp [Nat.pow_mod,hq]
    omega
  have hg : Nat.gcd 2 (q^2-1)=2 := by rw [Nat.gcd_rec,hm]; norm_num
  have hd : 2 ∣ q^2*((q^2)^2-1) := by
    apply dvd_mul_of_dvd_right
    apply Nat.dvd_of_mod_eq_zero
    have h : (q^2)^2%2=1 := by simp [Nat.pow_mod,hq]
    omega
  have hs : (q^2+1)*(q^2-1)=(q^2)^2-1 := by
    have hh : q^2-1+1=q^2 := Nat.sub_add_cancel hp
    have hh2 : (q^2)^2-1+1=(q^2)^2 := Nat.sub_add_cancel (one_le_pow₀ hp)
    nlinarith
  have hcard : Nat.card (E hdeg 1)*4=Nat.card (O hdeg 1) := by
    rw [rankTwo_elementary_order hdeg,card_full hdeg 1]
    change (q^2*((q^2)^2-1)/Nat.gcd 2 (q^2-1))*4 =
      2*q^2*(q^2+1)*∏i∈Finset.range 1,(q^(2*(i+1))-1)
    rw [hg]
    simp only [Finset.prod_range_one,Nat.zero_add,mul_one]
    calc
      (q^2*((q^2)^2-1)/2)*4 = 2*((q^2*((q^2)^2-1)/2)*2) := by ring
      _ = 2*(q^2*((q^2)^2-1)) := by rw [Nat.div_mul_cancel hd]
      _ = 2*q^2*(q^2+1)*(q^2-1) := by rw [← hs]; ring
  have hc := (E hdeg 1).card_mul_index
  have hn : Nat.card (E hdeg 1)≠0 := Nat.ne_of_gt Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) (hc.trans hcard.symm)

theorem rankTwo_elementary_eq_intrinsic_kernel (hdeg : Module.finrank F K = 2)
    (h2 : (2 : F)≠0) : E hdeg 1 =
      specialSubgroup (form hdeg 1) ⊓
        (spinorNorm (form hdeg 1) (polar_nondegenerate hdeg 1) h2).ker := by
  have he : E hdeg 1 =
      (determinantSpinor (form hdeg 1) (polar_nondegenerate hdeg 1) h2).ker := by
    apply le_antisymm (rankTwo_elementary_le_intrinsic_kernel hdeg h2)
    by_contra hn
    have hne : E hdeg 1 ≠
        (determinantSpinor (form hdeg 1) (polar_nondegenerate hdeg 1) h2).ker :=
      fun h => hn (h.ge)
    have hlt := Subgroup.index_strictAnti
      (lt_of_le_of_ne (rankTwo_elementary_le_intrinsic_kernel hdeg h2) hne)
    rw [rankTwo_elementary_index_odd hdeg h2,
      rankTwo_determinantSpinor_kernel_index hdeg h2] at hlt
    omega
  exact he.trans (determinantSpinor_kernel _ _ _)
end Minus

end Atlas.Orthogonal

import Atlas.Fischer.ResidueRankThree
import Atlas.Fischer.ResidueClassCriterion
import Atlas.Fischer.ResidueOrderThreeWitness

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem residueDistinguished_injective (S : Finset Omega) (hS : S.card≤2) :
    Function.Injective (residueDistinguishedElement S) := by
  haveI := residueGroup_primitive S hS
  exact residueDistinguished_injective_of_primitive S (residue_exists_order_three_pair S hS)

theorem residueDistinguished_order (S : Finset Omega) (hS : S.card≤2) (x : ResiduePoint S) :
    orderOf (residueDistinguishedElement S x)=2 :=
  residueDistinguished_order_of_order_three S hS (residue_exists_order_three_pair S hS) x

theorem residueDistinguishedClass_isConj_iff (S : Finset Omega) (hS : S.card≤2)
    (x : ResiduePoint S) (g : ResidueGroup S) :
    g ∈ Set.range (residueDistinguishedElement S) ↔ IsConj (residueDistinguishedElement S x) g := by
  constructor
  · rintro ⟨y,rfl⟩
    exact isConj_iff.mpr (residueDistinguishedElement_conjugate S (by omega) x y)
  · intro h
    obtain ⟨a,ha⟩ := isConj_iff.mp h
    exact ⟨a • x,(residueDistinguishedElement_covariance S a x).symm.trans ha⟩

/-- The exact two/three product orders of distinct original residue points survive quotienting. -/
theorem residueDistinguished_product_order (S : Finset Omega) (hS : S.card≤2)
    (x y : ResiduePoint S) (hxy : x≠y) :
    orderOf (residueDistinguishedElement S x * residueDistinguishedElement S y)=
      orderOf (x.val*y.val) := by
  have ho : orderOf (x.val*y.val)=2 ∨ orderOf (x.val*y.val)=3 := by
    obtain ⟨i,hi⟩ := x.property.1
    obtain ⟨j,hj⟩ := y.property.1
    have hij : i≠j := by
      intro he
      apply hxy
      apply Subtype.ext
      exact hi.symm.trans (he ▸ hj)
    rw [← hi,← hj,distinguishedRootElement_product_order i j hij]
    split_ifs <;> simp
  rcases ho with ho | ho
  · rw [ho]
    apply orderOf_eq_prime
    · let q := QuotientGroup.mk' (residueCentralElementary S)
      change (q (residuePointCentralizer S x) * q (residuePointCentralizer S y))^2=1
      rw [← map_mul,← map_pow]
      have hp : (residuePointCentralizer S x * residuePointCentralizer S y)^2=1 := by
        apply Subtype.ext
        change (x.val*y.val)^2=1
        rw [← ho]
        exact pow_orderOf_eq_one _
      rw [hp,map_one]
    · intro he
      have hi := inv_eq_of_mul_eq_one_right
        (show residueDistinguishedElement S y * residueDistinguishedElement S y=1 by
          simpa only [pow_two] using residueDistinguishedElement_square S y)
      have hsame : residueDistinguishedElement S x=residueDistinguishedElement S y :=
        (eq_inv_of_mul_eq_one_left he).trans hi
      exact hxy (residueDistinguished_injective S hS hsame)
  · rw [ho]
    exact residueDistinguished_product_order_three S x y ho

end Atlas.Fischer

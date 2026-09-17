import Atlas.Lattices.EisensteinBalancedHexadVectors
import Atlas.Lattices.EisensteinNineHexadVectors

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra

def eisensteinBalancedNineLift (c : TernaryBalancedWords) (k j : Fin 12) (b : ZMod 3) :
    EisensteinCoordinates := fun i => (ternarySignedLift (c.val.val i) : Eisenstein)+
      eisensteinTheta*eisensteinPhaseCorrection b*(ternarySignedLift (c.val.val k) : Eisenstein)*
        ((if i=k then 1 else 0)-(if i=j then 1 else 0))

def eisensteinBalancedNineVector (c : TernaryBalancedWords) (k j : Fin 12) (b : ZMod 3) :
    EisensteinCoordinates := eisensteinTheta • eisensteinBalancedNineLift c k j b

theorem eisensteinBalancedNineVector_mem (c : TernaryBalancedWords)
    (k j : Fin 12) (b : ZMod 3) :
    eisensteinBalancedNineVector c k j b ∈ eisensteinLeechModule := by
  rw [eisensteinBalancedNineVector,eisensteinLeechModule_theta_iff]
  constructor
  · have he : eisensteinWordResidue (eisensteinBalancedNineLift c k j b)=c.val.val := by
      ext i
      have hl : ∀ a : ZMod 3,eisensteinResidue (ternarySignedLift a : Eisenstein)=a := by
        decide +kernel
      simp [eisensteinBalancedNineLift,eisensteinWordResidue,hl,
        show eisensteinResidue eisensteinTheta=0 by decide +kernel]
    rw [he]
    exact c.val.prop
  · have he : ∑ i,eisensteinBalancedNineLift c k j b i=0 := by
      simp [eisensteinBalancedNineLift,Finset.sum_add_distrib,← Finset.mul_sum,
        Finset.sum_sub_distrib,← Int.cast_sum,ternaryBalanced_signed_sum c.val.val c.prop]
    rw [he]
    exact dvd_zero _

def eisensteinBalancedNineLatticeVector (c : TernaryBalancedWords)
    (k j : Fin 12) (b : ZMod 3) : EisensteinLattice :=
  ⟨eisensteinBalancedNineVector c k j b,eisensteinBalancedNineVector_mem c k j b⟩


theorem eisensteinBalancedNineVector_norm (c : TernaryBalancedWords)
    (k j : Fin 12) (hk : k ∈ ternarySupport c.val.val) (hj : j ∉ ternarySupport c.val.val)
    (b : ZMod 3) (hb : b≠0) :
    eisensteinNorm (eisensteinBalancedNineLatticeVector c k j b)=6 := by
  have hkj : k≠j := by intro h; exact hj (h ▸ hk)
  have hck : c.val.val k≠0 := (Finset.mem_filter.mp hk).2
  have hcj : c.val.val j=0 := by simpa [ternarySupport] using hj
  have hn : ∀ a : ZMod 3,
      (eisensteinToRational (eisensteinTheta*(ternarySignedLift a : Eisenstein))).norm =
        if a≠0 then 3 else 0 := by decide +kernel
  have hsmall : ∀ a d : ZMod 3,a≠0 → d≠0 →
      (eisensteinToRational (eisensteinTheta*((ternarySignedLift a : Eisenstein)+
        eisensteinTheta*eisensteinPhaseCorrection d*(ternarySignedLift a : Eisenstein)))).norm=3 ∧
      (eisensteinToRational (-eisensteinTheta^2*eisensteinPhaseCorrection d*
        (ternarySignedLift a : Eisenstein))).norm=9 := by decide +kernel
  have he (i : Fin 12) :
      (eisensteinToRational (eisensteinBalancedNineVector c k j b i)).norm =
        (if i ∈ ternarySupport c.val.val then (3 : ℚ) else 0)+(if i=j then 9 else 0) := by
    by_cases hik : i=k
    · subst i
      simpa [eisensteinBalancedNineVector,eisensteinBalancedNineLift,Pi.smul_apply,smul_eq_mul,hk,hkj]
        using (hsmall (c.val.val k) b hck hb).1
    · by_cases hij : i=j
      · subst i
        have hji := Ne.symm hkj
        have hkcases : c.val.val k=1 ∨ c.val.val k=2 :=
          (show ∀ a : ZMod 3,a≠0 → a=1 ∨ a=2 by decide +kernel) _ hck
        rcases hkcases with hckv|hckv <;>
          simpa [show (2 : ZMod 3)≠1 by decide,hckv,map_neg,QuadraticAlgebra.norm_neg,eisensteinBalancedNineVector,eisensteinBalancedNineLift,Pi.smul_apply,smul_eq_mul,hj,hji,
          hcj,ternarySignedLift,show (0 : ZMod 3)≠2 by decide,mul_assoc,pow_two]
          using (hsmall (c.val.val k) b hck hb).2
      · simpa [eisensteinBalancedNineVector,eisensteinBalancedNineLift,Pi.smul_apply,smul_eq_mul,hik,hij,
          ternarySupport] using hn (c.val.val i)
  rw [eisensteinNorm,eisensteinBilinear_self_sum_norm]
  change (2/9 : ℚ)*∑ i,(eisensteinToRational (eisensteinBalancedNineVector c k j b i)).norm=6
  simp_rw [he]
  norm_num [Finset.sum_add_distrib,ternarySupport_card,ternaryBalanced_weight _ c.prop]

end Atlas.Lattices

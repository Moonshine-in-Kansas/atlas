import Atlas.Codes.TernaryBalancedHexads
import Atlas.Codes.TernaryHexadProjection
import Atlas.Lattices.EisensteinTriadClassCriteria
import Atlas.Lattices.EisensteinShortLines

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra

def eisensteinBalancedHexadLift (c : TernaryBalancedWords) (j : Fin 12) :
    EisensteinCoordinates := fun i => (ternarySignedLift (c.val.val i) : Eisenstein) -
      if i=j then 3*(ternarySignedLift (c.val.val j) : Eisenstein) else 0

def eisensteinBalancedHexadVector (c : TernaryBalancedWords) (j : Fin 12) :
    EisensteinCoordinates := eisensteinTheta • eisensteinBalancedHexadLift c j

theorem eisensteinBalancedHexadLift_residue (c : TernaryBalancedWords) (j : Fin 12) :
    eisensteinWordResidue (eisensteinBalancedHexadLift c j)=c.val.val := by
  have hs : ∀ a : ZMod 3,eisensteinResidue (ternarySignedLift a : Eisenstein)=a := by
    decide +kernel
  ext i
  by_cases hi : i=j <;>
    simp [eisensteinWordResidue,eisensteinBalancedHexadLift,hi,hs,
      show eisensteinResidue 3=0 by decide +kernel]

theorem eisensteinBalancedHexadLift_sum (c : TernaryBalancedWords) (j : Fin 12) :
    ∑ i,eisensteinBalancedHexadLift c j i = -3*(ternarySignedLift (c.val.val j) : Eisenstein) := by
  have hs := ternaryBalanced_signed_sum c.val.val c.prop
  have he : (∑ i,(ternarySignedLift (c.val.val i) : Eisenstein))=0 := by
    exact_mod_cast hs
  simp [eisensteinBalancedHexadLift,Finset.sum_sub_distrib,he]

theorem eisensteinBalancedHexadVector_mem (c : TernaryBalancedWords) (j : Fin 12) :
    eisensteinBalancedHexadVector c j ∈ eisensteinLeechModule := by
  rw [eisensteinBalancedHexadVector,eisensteinLeechModule_theta_iff,
    eisensteinBalancedHexadLift_residue,eisensteinBalancedHexadLift_sum]
  exact ⟨c.val.prop,-(ternarySignedLift (c.val.val j) : Eisenstein),by ring⟩

def eisensteinBalancedHexadLatticeVector (c : TernaryBalancedWords) (j : Fin 12) :
    EisensteinLattice := ⟨eisensteinBalancedHexadVector c j,eisensteinBalancedHexadVector_mem c j⟩

theorem eisensteinBalancedHexadVector_norm (c : TernaryBalancedWords) (j : Fin 12)
    (hj : j ∈ ternarySupport c.val.val) :
    eisensteinNorm (eisensteinBalancedHexadLatticeVector c j)=6 := by
  have hn : c.val.val j≠0 := (Finset.mem_filter.mp hj).2
  have hscalar : ∀ a : ZMod 3,
      (eisensteinToRational (eisensteinTheta*(ternarySignedLift a : Eisenstein))).norm =
        if a=0 then 0 else 3 := by decide +kernel
  have hheavy : ∀ a : ZMod 3,a≠0 →
      (eisensteinToRational (eisensteinTheta*
        ((ternarySignedLift a : Eisenstein)-3*(ternarySignedLift a : Eisenstein)))).norm=12 := by
    decide +kernel
  have he (i : Fin 12) :
      (eisensteinToRational (eisensteinBalancedHexadVector c j i)).norm =
        (if i ∈ ternarySupport c.val.val then (3 : ℚ) else 0)+(if i=j then 9 else 0) := by
    by_cases hi : i=j
    · subst i
      simpa [eisensteinBalancedHexadVector,eisensteinBalancedHexadLift,hj,
        show (3 : ℚ)+9=12 by norm_num] using hheavy (c.val.val j) hn
    · simpa [eisensteinBalancedHexadVector,eisensteinBalancedHexadLift,hi,ternarySupport] using hscalar (c.val.val i)
  rw [eisensteinNorm,eisensteinBilinear_self_sum_norm]
  change (2/9 : ℚ)*(∑ i,(eisensteinToRational (eisensteinBalancedHexadVector c j i)).norm)=6
  simp_rw [he]
  norm_num [Finset.sum_add_distrib,ternarySupport_card,ternaryBalanced_weight _ c.prop]

def eisensteinBalancedHexadShellVector (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) : EisensteinShell 6 :=
  ⟨eisensteinBalancedHexadLatticeVector c j.val,eisensteinBalancedHexadVector_norm c j.val j.prop⟩

end Atlas.Lattices

import Atlas.Lattices.EisensteinHexadPhases
import Atlas.Lattices.EisensteinCongruenceCriteria

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra

/-- Two explicit nonzero phase choices giving the two constant-hexad norm-nine signs. -/
def eisensteinNineHexadLift (s : Finset (Fin 12)) (k j : Fin 12) (b : ZMod 3) :
    EisensteinCoordinates := fun i => (if i ∈ s then 1 else 0) +
      eisensteinTheta*eisensteinPhaseCorrection b*
        ((if i=k then 1 else 0)-(if i=j then 1 else 0))

def eisensteinNineHexadVector (s : Finset (Fin 12)) (k j : Fin 12) (b : ZMod 3) :
    EisensteinCoordinates := eisensteinTheta • eisensteinNineHexadLift s k j b

theorem eisensteinNineHexadVector_mem (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k j : Fin 12) (b : ZMod 3) :
    eisensteinNineHexadVector s k j b ∈ eisensteinLeechModule := by
  rw [eisensteinNineHexadVector,eisensteinLeechModule_theta_iff]
  constructor
  · have he : eisensteinWordResidue (eisensteinNineHexadLift s k j b)=ternaryTriadWord s := by
      ext i
      by_cases hi : i ∈ s <;> simp [eisensteinNineHexadLift,eisensteinWordResidue,
        ternaryTriadWord,hi,show eisensteinResidue eisensteinTheta=0 by decide +kernel]
    rw [he]
    exact ((mem_ternaryConstantHexads s).mp hs).2
  · have he : ∑ i,eisensteinNineHexadLift s k j b i=(s.card : Eisenstein) := by
      simp [eisensteinNineHexadLift,Finset.sum_add_distrib,← Finset.mul_sum,
        Finset.sum_sub_distrib]
    rw [he,((mem_ternaryConstantHexads s).mp hs).1]
    exact ⟨2,by norm_num⟩

def eisensteinNineHexadLatticeVector (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k j : Fin 12) (b : ZMod 3) : EisensteinLattice :=
  ⟨eisensteinNineHexadVector s k j b,eisensteinNineHexadVector_mem s hs k j b⟩

theorem eisensteinNineHexadVector_norm (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k j : Fin 12) (hk : k ∈ s) (hj : j ∉ s)
    (b : ZMod 3) (hb : b≠0) :
    eisensteinNorm (eisensteinNineHexadLatticeVector s hs k j b)=6 := by
  have hkj : k≠j := by intro h; exact hj (h ▸ hk)
  have he (i : Fin 12) :
      (eisensteinToRational (eisensteinNineHexadVector s k j b i)).norm =
        (if i ∈ s then (3 : ℚ) else 0)+(if i=j then 9 else 0) := by
    have hsmall : ∀ a : ZMod 3, a≠0 →
        (eisensteinToRational (eisensteinTheta*(1+eisensteinTheta*eisensteinPhaseCorrection a))).norm=3 ∧
        (eisensteinToRational (-eisensteinTheta^2*eisensteinPhaseCorrection a)).norm=9 := by
      decide +kernel
    by_cases hik : i=k
    · subst i
      simpa [eisensteinNineHexadVector,eisensteinNineHexadLift,Pi.smul_apply,smul_eq_mul,hk,hkj]
        using (hsmall b hb).1
    · by_cases hij : i=j
      · subst i
        have hji := Ne.symm hkj
        simpa [eisensteinNineHexadVector,eisensteinNineHexadLift,Pi.smul_apply,smul_eq_mul,hj,hji,
          mul_assoc,pow_two] using (hsmall b hb).2
      · by_cases his : i ∈ s <;>
          norm_num [eisensteinNineHexadVector,eisensteinNineHexadLift,Pi.smul_apply,smul_eq_mul,his,hik,hij,
            eisensteinToRational,eisensteinTheta,eisensteinOmega,QuadraticAlgebra.omega,QuadraticAlgebra.norm_def]
  rw [eisensteinNorm,eisensteinBilinear_self_sum_norm]
  change (2/9 : ℚ)*∑ i,(eisensteinToRational (eisensteinNineHexadVector s k j b i)).norm=6
  simp_rw [he]
  norm_num [Finset.sum_add_distrib,((mem_ternaryConstantHexads s).mp hs).1]

end Atlas.Lattices

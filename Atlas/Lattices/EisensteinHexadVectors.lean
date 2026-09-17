import Atlas.Codes.TernaryConstantHexads
import Atlas.Lattices.EisensteinFrameSpanning

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra

/-- A heavy hexad vector: theta times the support indicator minus three at one support point. -/
def eisensteinHexadLift (s : Finset (Fin 12)) (i : Fin 12) : EisensteinCoordinates :=
  fun j => (if j ∈ s then 1 else 0) - (if j = i then 3 else 0)

def eisensteinHexadVector (s : Finset (Fin 12)) (i : Fin 12) : EisensteinCoordinates :=
  eisensteinTheta • eisensteinHexadLift s i

theorem eisensteinHexadLift_sum (s : Finset (Fin 12)) (i : Fin 12) :
    ∑ j, eisensteinHexadLift s i j = (s.card : Eisenstein) - 3 := by
  simp [eisensteinHexadLift, Finset.sum_sub_distrib]

theorem eisensteinHexadVector_mem (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i : Fin 12) :
    eisensteinHexadVector s i ∈ eisensteinLeechModule := by
  obtain ⟨hcard,hcode⟩ := (mem_ternaryConstantHexads s).mp hs
  refine ⟨0,eisensteinHexadLift s i,?_,?_,?_⟩
  · intro j; simp [eisensteinHexadVector]
  · have he : eisensteinWordResidue (eisensteinHexadLift s i) = ternaryTriadWord s := by
      ext j
      by_cases hj : j = i <;> by_cases hjs : j ∈ s <;>
        simp [eisensteinWordResidue,eisensteinHexadLift,ternaryTriadWord,hj,hjs, show eisensteinResidue 3 = 0 by decide +kernel]
    rwa [he]
  · refine ⟨1,?_⟩
    simp [eisensteinHexadVector,Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,
      eisensteinHexadLift_sum,hcard]
    ring

def eisensteinHexadLatticeVector (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i : Fin 12) : EisensteinLattice :=
  ⟨eisensteinHexadVector s i,eisensteinHexadVector_mem s hs i⟩

theorem eisensteinHexadVector_norm (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i : Fin 12) (hi : i ∈ s) :
    eisensteinNorm (eisensteinHexadLatticeVector s hs i) = 6 := by
  have hcard := ((mem_ternaryConstantHexads s).mp hs).1
  have he (j : Fin 12) :
      (eisensteinToRational (eisensteinHexadVector s i j)).norm =
        (if j ∈ s then (3 : ℚ) else 0) + (if j = i then 9 else 0) := by
    by_cases hji : j=i
    · subst j
      norm_num [eisensteinHexadVector,eisensteinHexadLift,Pi.smul_apply,smul_eq_mul,hi,
        eisensteinToRational,eisensteinTheta,eisensteinOmega,QuadraticAlgebra.omega,QuadraticAlgebra.norm_def]
    · by_cases hj : j ∈ s <;>
        norm_num [eisensteinHexadVector,eisensteinHexadLift,Pi.smul_apply,smul_eq_mul,hji,hj,
          eisensteinToRational,eisensteinTheta,eisensteinOmega,QuadraticAlgebra.omega,QuadraticAlgebra.norm_def]
  rw [eisensteinNorm,eisensteinBilinear_self_sum_norm]
  change (2/9 : ℚ) * ∑ j, (eisensteinToRational (eisensteinHexadVector s i j)).norm = 6
  simp_rw [he]
  norm_num [Finset.sum_add_distrib,hcard]

def eisensteinHexadShellVector (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i : Fin 12) (hi : i ∈ s) : EisensteinShell 6 :=
  ⟨eisensteinHexadLatticeVector s hs i,eisensteinHexadVector_norm s hs i hi⟩

end Atlas.Lattices

import Atlas.Lattices.EisensteinFrames
import Atlas.Lattices.EisensteinPhases
import Atlas.Codes.TernaryGolayTriads

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra

/-- The norm-six triad vectors; their phases need not extend to a codeword. -/
def eisensteinTriadVector (s : Finset (Fin 12)) (a : TernaryWord) : EisensteinCoordinates :=
  fun i => if i ∈ s then 3*eisensteinPhase (a i) else 0

theorem eisensteinTriadVector_mem (s : Finset (Fin 12)) (hs : s.card=3)
    (a : TernaryWord) : eisensteinTriadVector s a ∈ eisensteinLeechModule := by
  let u : EisensteinCoordinates := fun i =>
    if i ∈ s then -eisensteinTheta*eisensteinPhase (a i) else 0
  refine ⟨0,u,?_,?_,?_⟩
  · intro i
    simp only [eisensteinTriadVector,u,Int.cast_zero,zero_add]
    split_ifs <;> simp [← mul_assoc,← pow_two,eisensteinTheta_sq]
  · have he : eisensteinWordResidue u = 0 := by
      funext i
      by_cases hi : i ∈ s <;> simp [u,eisensteinWordResidue,hi,
        show eisensteinResidue eisensteinTheta = 0 by decide +kernel]
    rw [he]
    exact Submodule.zero_mem _
  · have hd : eisensteinTheta ∣ ∑ i ∈ s,eisensteinPhase (a i) := by
      apply (eisensteinResidue_eq_zero _).mp
      simp [hs]
      decide
    obtain ⟨b,hb⟩ := hd
    refine ⟨b,?_⟩
    simp only [eisensteinTriadVector,Int.cast_zero,mul_zero,add_zero]
    rw [Finset.sum_ite_mem]
    rw [Finset.univ_inter,← Finset.mul_sum,hb]
    ring

def eisensteinTriadLatticeVector (s : Finset (Fin 12)) (hs : s.card=3)
    (a : TernaryWord) : EisensteinLattice :=
  ⟨eisensteinTriadVector s a,eisensteinTriadVector_mem s hs a⟩

theorem eisensteinTriadVector_norm (s : Finset (Fin 12)) (hs : s.card=3)
    (a : TernaryWord) : eisensteinNorm (eisensteinTriadLatticeVector s hs a) = 6 := by
  rw [eisensteinNorm,eisensteinBilinear_self]
  have he (i : Fin 12) :
      ((eisensteinCoordinateEmbedding (eisensteinTriadVector s a) i).re ^ 2 -
        (eisensteinCoordinateEmbedding (eisensteinTriadVector s a) i).re *
          (eisensteinCoordinateEmbedding (eisensteinTriadVector s a) i).im +
        (eisensteinCoordinateEmbedding (eisensteinTriadVector s a) i).im ^ 2) =
      if i ∈ s then (9 : ℚ) else 0 := by
    by_cases hi : i ∈ s
    · have hphase : ∀ b : ZMod 3,
          (eisensteinToRational (3*eisensteinPhase b)).re^2 -
            (eisensteinToRational (3*eisensteinPhase b)).re *
              (eisensteinToRational (3*eisensteinPhase b)).im +
            (eisensteinToRational (3*eisensteinPhase b)).im^2 = 9 := by decide +kernel
      simpa [eisensteinCoordinateEmbedding,eisensteinTriadVector,hi] using hphase (a i)
    · simp [eisensteinCoordinateEmbedding,eisensteinTriadVector,hi]
  change (2/9 : ℚ) * ∑ i,
    ((eisensteinCoordinateEmbedding (eisensteinTriadVector s a) i).re ^ 2 -
      (eisensteinCoordinateEmbedding (eisensteinTriadVector s a) i).re *
        (eisensteinCoordinateEmbedding (eisensteinTriadVector s a) i).im +
      (eisensteinCoordinateEmbedding (eisensteinTriadVector s a) i).im ^ 2) = 6
  simp_rw [he]
  norm_num [hs]

def eisensteinTriadShellVector (s : Finset (Fin 12)) (hs : s.card=3)
    (a : TernaryWord) : EisensteinShell 6 :=
  ⟨eisensteinTriadLatticeVector s hs a,eisensteinTriadVector_norm s hs a⟩

def eisensteinTriadFrame (s : Finset (Fin 12)) (hs : s.card=3)
    (a : TernaryWord) : EisensteinFrame :=
  eisensteinFrameOfVector (eisensteinTriadShellVector s hs a)

end Atlas.Lattices

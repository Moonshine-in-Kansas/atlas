import Atlas.Lattices.EisensteinBalancedClassPhases
import Atlas.Lattices.EisensteinThreeCongruence
import Atlas.Conway.EisensteinStandardFrame

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

theorem eisensteinBalancedClass_same_phase (c : TernaryBalancedWords)
    (j k : ternarySupport c.val.val) (a : EisensteinBalancedPhase c) :
    eisensteinClass (eisensteinBalancedPhasedLatticeVector c j a)=
      eisensteinClass (eisensteinBalancedPhasedLatticeVector c k a) ↔
      c.val.val j.val=c.val.val k.val := by
  rw [eisensteinClass_theta_difference_iff _ _ _ _
    (eisensteinBalancedPhasedVector_theta c j a) (eisensteinBalancedPhasedVector_theta c k a)]
  let v : EisensteinCoordinates :=
    -Pi.single j.val ((ternarySignedLift (c.val.val j.val) : Eisenstein)*
      eisensteinPhase (eisensteinBalancedPhaseWord c a j.val)) +
    Pi.single k.val ((ternarySignedLift (c.val.val k.val) : Eisenstein)*
      eisensteinPhase (eisensteinBalancedPhaseWord c a k.val))
  have he : eisensteinBalancedPhasedLift c j a-eisensteinBalancedPhasedLift c k a =
      (3 : Eisenstein) • v := by
    funext i
    by_cases hj : i=j.val <;> by_cases hk : i=k.val <;>
      simp_all [eisensteinBalancedPhasedLift,eisensteinDiagonal,eisensteinBalancedHexadLift,
        v,Pi.single_apply] <;> ring
  rw [he,eisensteinLeechModule_three_iff,← eisensteinResidue_eq_zero]
  have hs : ∀ b : ZMod 3,eisensteinResidue (ternarySignedLift b : Eisenstein)=b := by decide +kernel
  simp [v,Finset.sum_add_distrib,Finset.sum_neg_distrib,hs,neg_add_eq_zero]

theorem eisensteinBalancedPhasedVector_global (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (a b : EisensteinBalancedPhase c) (r : ZMod 3)
    (hr : ∀ i : ternarySupport c.val.val,b.val i=a.val i+r) :
    eisensteinBalancedPhasedLatticeVector c j b =
      eisensteinPhase r • eisensteinBalancedPhasedLatticeVector c j a := by
  apply Subtype.ext
  funext i
  change eisensteinPhase (eisensteinBalancedPhaseWord c b i)*eisensteinBalancedHexadVector c j.val i =
    eisensteinPhase r*(eisensteinPhase (eisensteinBalancedPhaseWord c a i)*
      eisensteinBalancedHexadVector c j.val i)
  by_cases hi : i ∈ ternarySupport c.val.val
  · simp only [eisensteinBalancedPhaseWord,dif_pos hi,hr,eisensteinPhase_add]
    ring
  · have hz : c.val.val i=0 := by simpa [ternarySupport] using hi
    have hij : i≠j.val := by intro h; subst i; exact hi j.prop
    simp [eisensteinBalancedHexadVector,eisensteinBalancedHexadLift,hij,hz,ternarySignedLift,
      show (0 : ZMod 3)≠2 by decide]

/-- The exact oriented-class criterion: the heavy positions have the same sign
and the phase assignments differ by a single global phase. -/
theorem eisensteinBalancedClass_eq_iff (c : TernaryBalancedWords)
    (j k : ternarySupport c.val.val) (a b : EisensteinBalancedPhase c) :
    eisensteinClass (eisensteinBalancedPhasedLatticeVector c j a)=
      eisensteinClass (eisensteinBalancedPhasedLatticeVector c k b) ↔
    c.val.val j.val=c.val.val k.val ∧
      ∃ r : ZMod 3,∀ i : ternarySupport c.val.val,b.val i=a.val i+r := by
  constructor
  · intro h
    obtain ⟨r,hr⟩ := eisensteinBalancedClass_phases c j k a b h
    have hb : eisensteinClass (eisensteinBalancedPhasedLatticeVector c k b)=
        eisensteinClass (eisensteinBalancedPhasedLatticeVector c k a) := by
      rw [eisensteinBalancedPhasedVector_global c k a b r hr,eisensteinClass_phase]
    exact ⟨(eisensteinBalancedClass_same_phase c j k a).mp (h.trans hb),r,hr⟩
  · rintro ⟨hj,r,hr⟩
    rw [eisensteinBalancedPhasedVector_global c k a b r hr,eisensteinClass_phase]
    exact (eisensteinBalancedClass_same_phase c j k a).mpr hj

end Atlas.Conway

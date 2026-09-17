import Atlas.Conway.EisensteinBalancedClassModel

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

theorem eisensteinBalancedSourceBase_card : ({0,1,7} : Finset (Fin 12)).card=3 := by decide

def eisensteinBalancedSourceFiber (p : EisensteinBalancedClassParameter) :
    EisensteinClassFiber 6 (eisensteinClass (eisensteinTriadLatticeVector {0,1,7} eisensteinBalancedSourceBase_card 0)) :=
  ⟨eisensteinBalancedSourceShell p,(eisensteinBalancedSourceVector_class p).symm⟩

theorem eisensteinBalancedSourceFiber_bijective :
    Function.Bijective eisensteinBalancedSourceFiber := by
  classical
  letI : Finite (EisensteinClassFiber 6
    (eisensteinClass (eisensteinTriadLatticeVector {0,1,7} eisensteinBalancedSourceBase_card 0))) := by
      unfold EisensteinClassFiber
      infer_instance
  letI := Fintype.ofFinite (EisensteinClassFiber 6
    (eisensteinClass (eisensteinTriadLatticeVector {0,1,7} eisensteinBalancedSourceBase_card 0)))
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro p q hpq
    exact eisensteinBalancedSourceVector_injective
      (congrArg (fun x => x.val.val) hpq)
  · have hc := eisenstein_six_class_card
      (eisensteinClass (eisensteinTriadLatticeVector {0,1,7} eisensteinBalancedSourceBase_card 0))
      (Finset.mem_image.mpr ⟨eisensteinTriadShellVector {0,1,7} eisensteinBalancedSourceBase_card 0,Finset.mem_univ _,rfl⟩)
    have hs : Nat.card EisensteinBalancedClassParameter=36 := by
      simp [EisensteinBalancedClassParameter,Nat.card_prod]
    exact (Nat.card_eq_fintype_card (α := EisensteinBalancedClassParameter)).symm.trans
      (hs.trans (hc.symm.trans (Nat.card_eq_fintype_card)))

def eisensteinBalancedProfileVector (p : EisensteinBalancedClassParameter) : EisensteinCoordinates :=
  fun i => ∑ j,eisensteinFourierNumerator i j *
    (if p.1.val<2 then eisensteinTriadUnits (eisensteinBalancedSourceTriad p.1)
      (eisensteinBalancedSourcePhase p) j else
      -eisensteinTriadUnits (eisensteinBalancedSourceTriad p.1) (eisensteinBalancedSourcePhase p) j)

theorem eisensteinBalancedProfileVector_fourier : ∀ p : EisensteinBalancedClassParameter,
    eisensteinFourier (eisensteinCoordinateEmbedding (eisensteinBalancedSourceVector p).val)=
      eisensteinCoordinateEmbedding (eisensteinBalancedProfileVector p) := by
  rintro ⟨b,a,d⟩
  rw [eisensteinFourier_apply]
  fin_cases b <;> fin_cases a <;> fin_cases d <;> decide +kernel

def eisensteinBalancedProfileCount (p : EisensteinBalancedClassParameter) (n : ℤ) : ℕ :=
  (Finset.univ.filter (fun i => (eisensteinBalancedProfileVector p i).norm=n)).card

/-- The 36 vectors split into nine heavy-hexad and twenty-seven weight-nine vectors. -/
theorem eisensteinBalancedProfile_counts :
    (Finset.univ.filter (fun p : EisensteinBalancedClassParameter =>
      eisensteinBalancedProfileCount p 12=1)).card=9 ∧
    (Finset.univ.filter (fun p : EisensteinBalancedClassParameter =>
      eisensteinBalancedProfileCount p 3=9)).card=27 := by decide +kernel

theorem eisensteinBalancedProfile_patterns : ∀ p : EisensteinBalancedClassParameter,
    (eisensteinBalancedProfileCount p 0=6 ∧ eisensteinBalancedProfileCount p 3=5 ∧
      eisensteinBalancedProfileCount p 12=1) ∨
    (eisensteinBalancedProfileCount p 0=3 ∧ eisensteinBalancedProfileCount p 3=9) := by
  decide +kernel

end Atlas.Conway

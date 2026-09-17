import Atlas.Conway.EisensteinBalancedFourier

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

abbrev EisensteinBalancedClassParameter := Fin 4 × ZMod 3 × ZMod 3

def eisensteinBalancedSourceTriad : Fin 4 → Finset (Fin 12) :=
  ![{0,1,7},{2,3,8},{4,10,11},{5,6,9}]

def eisensteinBalancedSourceMark : Fin 4 → Fin 3 → Fin 12 :=
  ![![0,1,7],![2,3,8],![4,10,11],![5,6,9]]

theorem eisensteinBalancedSourceTriad_card (b : Fin 4) :
    (eisensteinBalancedSourceTriad b).card=3 := by revert b; decide +kernel

def eisensteinBalancedSourcePhase (p : EisensteinBalancedClassParameter) : TernaryWord :=
  fun i => if i=eisensteinBalancedSourceMark p.1 0 then p.2.1 else
    if i=eisensteinBalancedSourceMark p.1 1 then p.2.2 else
      if i=eisensteinBalancedSourceMark p.1 2 then -p.2.1-p.2.2 else 0

def eisensteinBalancedSourceVector (p : EisensteinBalancedClassParameter) : EisensteinLattice :=
  let x := eisensteinTriadLatticeVector (eisensteinBalancedSourceTriad p.1)
    (eisensteinBalancedSourceTriad_card p.1) (eisensteinBalancedSourcePhase p)
  if p.1.val<2 then x else -x

theorem eisensteinBalancedSourceVector_norm : ∀ p : EisensteinBalancedClassParameter,
    eisensteinNorm (eisensteinBalancedSourceVector p)=6 := by decide +kernel

def eisensteinBalancedSourceShell (p : EisensteinBalancedClassParameter) : EisensteinShell 6 :=
  ⟨eisensteinBalancedSourceVector p,eisensteinBalancedSourceVector_norm p⟩

theorem eisensteinBalancedSourceVector_class (p : EisensteinBalancedClassParameter) :
    eisensteinClass (eisensteinTriadLatticeVector {0,1,7} (by decide) 0) =
      eisensteinClass (eisensteinBalancedSourceVector p) := by
  unfold eisensteinBalancedSourceVector
  split_ifs with h
  · apply (eisensteinTriadClass_eq_iff _ _ _ _ _ _).mpr
    have hh : ∀ q : EisensteinBalancedClassParameter,q.1.val<2 →
        (ternaryTriadWord {0,1,7}-ternaryTriadWord (eisensteinBalancedSourceTriad q.1) ∈ ternaryGolay ∧
          (∑ i ∈ ({0,1,7} : Finset (Fin 12)),(0 : TernaryWord) i)=
            ∑ i ∈ eisensteinBalancedSourceTriad q.1,eisensteinBalancedSourcePhase q i) := by
      simp only [ternaryGolay_mem_iff_decode]
      decide +kernel
    exact hh p h
  · rw [map_neg]
    apply (eisensteinTriadClass_eq_neg_iff _ _ _ _ _ _).mpr
    have hh : ∀ q : EisensteinBalancedClassParameter,¬q.1.val<2 →
        (ternaryTriadWord {0,1,7}+ternaryTriadWord (eisensteinBalancedSourceTriad q.1) ∈ ternaryGolay ∧
          (∑ i ∈ ({0,1,7} : Finset (Fin 12)),(0 : TernaryWord) i)+
            (∑ i ∈ eisensteinBalancedSourceTriad q.1,eisensteinBalancedSourcePhase q i)=0) := by
      simp only [ternaryGolay_mem_iff_decode]
      decide +kernel
    exact hh p h

theorem eisensteinBalancedSourceVector_injective :
    Function.Injective eisensteinBalancedSourceVector := by
  have h : ∀ p q : EisensteinBalancedClassParameter,
      (eisensteinBalancedSourceVector p).val=(eisensteinBalancedSourceVector q).val → p=q := by
    decide +kernel
  intro p q hpq
  exact h p q (congrArg Subtype.val hpq)

end Atlas.Conway

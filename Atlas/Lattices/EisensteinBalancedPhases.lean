import Atlas.Lattices.EisensteinBalancedHexadVectors

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra

abbrev EisensteinBalancedPhase (c : TernaryBalancedWords) :=
  (ternaryHexadFunctional (ternaryBalancedSixWord c)).ker

def eisensteinBalancedPhaseWord (c : TernaryBalancedWords) (a : EisensteinBalancedPhase c) :
    TernaryWord := fun i => if h : i ∈ ternarySupport c.val.val then a.val ⟨i,h⟩ else 0

def eisensteinBalancedPhasedVector (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (a : EisensteinBalancedPhase c) : EisensteinCoordinates :=
  eisensteinDiagonal (eisensteinBalancedPhaseWord c a) (eisensteinBalancedHexadVector c j.val)

theorem eisensteinBalancedPhasedVector_mem (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (a : EisensteinBalancedPhase c) :
    eisensteinBalancedPhasedVector c j a ∈ eisensteinLeechModule := by
  obtain ⟨t,ht⟩ := ternaryHexadPhase_lift (ternaryBalancedSixWord c) a.val a.prop
  convert eisensteinDiagonal_mem t (eisensteinBalancedHexadVector_mem c j.val) using 1
  funext i
  change eisensteinPhase (eisensteinBalancedPhaseWord c a i)*eisensteinBalancedHexadVector c j.val i =
    eisensteinPhase (t.val i)*eisensteinBalancedHexadVector c j.val i
  by_cases hi : i ∈ ternarySupport c.val.val
  · have hh := ht ⟨i,hi⟩
    simp only [eisensteinBalancedPhaseWord,dif_pos hi,hh]
  · have hz : c.val.val i=0 := by simpa [ternarySupport] using hi
    have hij : i≠j.val := by intro he; subst i; exact hi j.prop
    simp [eisensteinBalancedHexadVector,eisensteinBalancedHexadLift,hij,hz,ternarySignedLift,
      show (0 : ZMod 3)≠2 by decide]

def eisensteinBalancedPhasedLatticeVector (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (a : EisensteinBalancedPhase c) : EisensteinLattice :=
  ⟨eisensteinBalancedPhasedVector c j a,eisensteinBalancedPhasedVector_mem c j a⟩

theorem eisensteinBalancedPhasedVector_norm (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (a : EisensteinBalancedPhase c) :
    eisensteinNorm (eisensteinBalancedPhasedLatticeVector c j a)=6 := by
  have hp : ∀ b : ZMod 3,(eisensteinToRational (eisensteinPhase b)).norm=1 := by decide +kernel
  have he : eisensteinNorm (eisensteinBalancedPhasedLatticeVector c j a) =
      eisensteinNorm (eisensteinBalancedHexadLatticeVector c j.val) := by
    simp only [eisensteinNorm,eisensteinBilinear_self_sum_norm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    change (eisensteinToRational (eisensteinPhase (eisensteinBalancedPhaseWord c a i)*
      eisensteinBalancedHexadVector c j.val i)).norm =
        (eisensteinToRational (eisensteinBalancedHexadVector c j.val i)).norm
    rw [map_mul,map_mul,hp,one_mul]
  rw [he]
  exact eisensteinBalancedHexadVector_norm c j.val j.prop

def eisensteinBalancedPhasedShellVector (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (a : EisensteinBalancedPhase c) : EisensteinShell 6 :=
  ⟨eisensteinBalancedPhasedLatticeVector c j a,eisensteinBalancedPhasedVector_norm c j a⟩

abbrev EisensteinBalancedParameters :=
  (c : TernaryBalancedWords) × (ternarySupport c.val.val) × EisensteinBalancedPhase c

theorem eisensteinBalancedParameters_card : Nat.card EisensteinBalancedParameters=320760 := by
  classical
  letI := Fintype.ofFinite TernaryBalancedWords
  rw [Nat.card_sigma]
  have hc (c : TernaryBalancedWords) :
      Nat.card ((ternarySupport c.val.val) × EisensteinBalancedPhase c)=1458 := by
    rw [Nat.card_prod,Nat.card_eq_fintype_card (α := ternarySupport c.val.val),
      Fintype.card_coe,ternarySupport_card,ternaryBalanced_weight _ c.prop]
    rw [show Nat.card (EisensteinBalancedPhase c)=243 from ternaryHexadPhase_card (ternaryBalancedSixWord c)]
  simp_rw [hc]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,
    ternaryBalancedWords_card]
  norm_num

end Atlas.Lattices

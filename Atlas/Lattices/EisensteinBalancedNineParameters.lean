import Atlas.Lattices.EisensteinBalancedNineVectors
import Atlas.Codes.TernaryHexadAffinePhases

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators

def eisensteinBalancedNineSign (b : Bool) : Eisenstein := if b then -1 else 1

def ternaryBalancedNineSign (b : Bool) : ZMod 3 := if b then -1 else 1

abbrev EisensteinBalancedNinePhase (c : TernaryBalancedWords) (b : Bool) :=
  TernaryHexadAffinePhase (ternaryBalancedSixWord c) (ternaryBalancedNineSign b)

abbrev EisensteinBalancedNineParameters :=
  (c : TernaryBalancedWords) × {j : Fin 12 // j ∉ ternarySupport c.val.val} ×
    (b : Bool) × EisensteinBalancedNinePhase c b × ZMod 3

theorem eisensteinBalancedNineParameters_card : Nat.card EisensteinBalancedNineParameters=1924560 := by
  classical
  letI := Fintype.ofFinite TernaryBalancedWords
  rw [Nat.card_sigma]
  have ho (c : TernaryBalancedWords) : Nat.card {j : Fin 12 // j ∉ ternarySupport c.val.val}=6 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe,
      ternarySupport_card,ternaryBalanced_weight _ c.prop]
  have hc (c : TernaryBalancedWords) :
      Nat.card ({j : Fin 12 // j ∉ ternarySupport c.val.val} ×
        ((b : Bool) × EisensteinBalancedNinePhase c b × ZMod 3))=8748 := by
    rw [Nat.card_prod,ho,Nat.card_sigma]
    have hb (b : Bool) : Nat.card (EisensteinBalancedNinePhase c b × ZMod 3)=729 := by
      rw [Nat.card_prod,ternaryHexadAffinePhase_card]
      norm_num
    simp_rw [hb]
    norm_num
  simp_rw [hc]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,
    ternaryBalancedWords_card]
  norm_num

def eisensteinBalancedNinePhaseWord (c : TernaryBalancedWords) (b : Bool)
    (a : EisensteinBalancedNinePhase c b) : TernaryWord :=
  fun i => if h : i ∈ ternarySupport c.val.val then a.val ⟨i,h⟩ else 0

def eisensteinBalancedNineParameterLift (p : EisensteinBalancedNineParameters) :
    EisensteinCoordinates := fun i =>
  (ternarySignedLift (p.1.val.val i) : Eisenstein)*
    eisensteinPhase (eisensteinBalancedNinePhaseWord p.1 p.2.2.1 p.2.2.2.1 i)+
      if i=p.2.1.val then eisensteinTheta*eisensteinBalancedNineSign p.2.2.1*
        eisensteinPhase p.2.2.2.2 else 0

def eisensteinBalancedNineParameterVector (p : EisensteinBalancedNineParameters) :
    EisensteinCoordinates := eisensteinTheta • eisensteinBalancedNineParameterLift p

end Atlas.Lattices

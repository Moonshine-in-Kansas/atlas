import Atlas.Conway.EisensteinNineHexadPartitions
import Atlas.Conway.EisensteinNineHexadFrameSigns
import Atlas.Conway.EisensteinHexadFamily

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

local instance eisensteinNineHexadFamilyPhaseAction : MulAction (Multiplicative ternaryGolay) EisensteinFrame :=
  MulAction.compHom EisensteinFrame eisensteinPhaseIsometries

def eisensteinNineHexadPairOutside (p : TernaryConstantHexadPair) : Fin 12 :=
  (Finset.card_pos.mp (show 0 < ((eisensteinHexadPairSupport p)ᶜ).card by
    rw [Finset.card_compl, ((mem_ternaryConstantHexads _).mp (eisensteinHexadPairSupport_mem p)).1]
    decide)).choose

theorem eisensteinNineHexadPairOutside_mem (p : TernaryConstantHexadPair) :
    eisensteinNineHexadPairOutside p ∉ eisensteinHexadPairSupport p :=
  Finset.mem_compl.mp (Finset.card_pos.mp
    (show 0 < ((eisensteinHexadPairSupport p)ᶜ).card by
      rw [Finset.card_compl, ((mem_ternaryConstantHexads _).mp (eisensteinHexadPairSupport_mem p)).1]
      decide)).choose_spec

def eisensteinNineHexadPairFrame (b : ZMod 3) (hb : b≠0)
    (p : TernaryConstantHexadPair) : EisensteinFrame :=
  eisensteinNineHexadFrame _ (eisensteinHexadPairSupport_mem p)
    _ _ (eisensteinHexadPairPoint_mem p) (eisensteinNineHexadPairOutside_mem p) b hb

variable (b : ZMod 3) (hb : b≠0)

def eisensteinNineHexadPairOrbit (p : TernaryConstantHexadPair) : Finset EisensteinFrame :=
  (Set.toFinite (MulAction.orbit (Multiplicative ternaryGolay) (eisensteinNineHexadPairFrame b hb p))).toFinset

theorem eisensteinNineHexadPairOrbit_mem (p : TernaryConstantHexadPair) (F : EisensteinFrame) :
    F ∈ eisensteinNineHexadPairOrbit b hb p ↔ ∃ t : Multiplicative ternaryGolay,
      eisensteinPhaseIsometries t • eisensteinNineHexadPairFrame b hb p=F := by
  simp only [eisensteinNineHexadPairOrbit,Set.Finite.mem_toFinset]
  rfl

theorem eisensteinNineHexadPairOrbit_card (p : TernaryConstantHexadPair) :
    (eisensteinNineHexadPairOrbit b hb p).card=243 := by
  have hc := eisensteinNineHexadPhaseOrbit_card _ (eisensteinHexadPairSupport_mem p)
    _ _ (eisensteinHexadPairPoint_mem p) (eisensteinNineHexadPairOutside_mem p) b hb
  change Nat.card (MulAction.orbit (Multiplicative ternaryGolay) (eisensteinNineHexadPairFrame b hb p))=243 at hc
  rw [Nat.card_coe_set_eq] at hc
  unfold eisensteinNineHexadPairOrbit
  rw [← Set.ncard_eq_toFinset_card]
  exact hc

theorem eisensteinNineHexadPairOrbit_disjoint (p q : TernaryConstantHexadPair) (hpq : p≠q) :
    Disjoint (eisensteinNineHexadPairOrbit b hb p) (eisensteinNineHexadPairOrbit b hb q) := by
  apply Finset.disjoint_left.mpr
  intro F hF hG
  obtain ⟨t,ht⟩ := (eisensteinNineHexadPairOrbit_mem b hb p F).mp hF
  obtain ⟨u,hu⟩ := (eisensteinNineHexadPairOrbit_mem b hb q F).mp hG
  have he : eisensteinPhaseIsometries (u⁻¹*t) • eisensteinNineHexadPairFrame b hb p=eisensteinNineHexadPairFrame b hb q := by
    rw [map_mul,mul_smul,ht,← hu,← mul_smul,← map_mul,inv_mul_cancel,map_one,one_smul]
  have hp := eisensteinNineHexadFrame_phase_partition _ _ (eisensteinHexadPairSupport_mem q)
    (eisensteinHexadPairSupport_mem p) _ _ _ _ (eisensteinHexadPairPoint_mem q)
    (eisensteinNineHexadPairOutside_mem q) (eisensteinHexadPairPoint_mem p)
    (eisensteinNineHexadPairOutside_mem p) b b hb hb (u⁻¹*t).toAdd he
  rw [eisensteinHexadPairSupport_pair,eisensteinHexadPairSupport_pair] at hp
  exact hpq (Subtype.ext hp.symm)

/-- The intrinsic family parametrized by complementary constant hexads and their code phases. -/
def eisensteinNineHexadFamily : Finset EisensteinFrame :=
  Finset.univ.biUnion (eisensteinNineHexadPairOrbit b hb)

theorem eisensteinNineHexadFamily_card : (eisensteinNineHexadFamily b hb).card=2673 := by
  rw [eisensteinNineHexadFamily,Finset.card_biUnion]
  · simp only [eisensteinNineHexadPairOrbit_card,Finset.sum_const,Finset.card_univ,
      Fintype.card_coe,ternaryConstantHexadPairs_card,nsmul_eq_mul]
    norm_num
  · intro p hp q hq hpq
    exact eisensteinNineHexadPairOrbit_disjoint b hb p q hpq

/-- The two nonzero correction choices give disjoint actual frame families. -/
theorem eisensteinNineHexadFamily_disjoint (d : ZMod 3) (hd : d≠0) (hbd : b≠d) :
    Disjoint (eisensteinNineHexadFamily b hb) (eisensteinNineHexadFamily d hd) := by
  apply Finset.disjoint_left.mpr
  intro F hF hG
  obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hF
  obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp hG
  obtain ⟨t,ht⟩ := (eisensteinNineHexadPairOrbit_mem b hb p F).mp hp
  obtain ⟨u,hu⟩ := (eisensteinNineHexadPairOrbit_mem d hd q F).mp hq
  have he : eisensteinPhaseIsometries (u⁻¹*t) • eisensteinNineHexadPairFrame b hb p=
      eisensteinNineHexadPairFrame d hd q := by
    rw [map_mul,mul_smul,ht,← hu,← mul_smul,← map_mul,inv_mul_cancel,map_one,one_smul]
  have hpq := eisensteinNineHexadFrame_phase_partition _ _ (eisensteinHexadPairSupport_mem q)
    (eisensteinHexadPairSupport_mem p) _ _ _ _ (eisensteinHexadPairPoint_mem q)
    (eisensteinNineHexadPairOutside_mem q) (eisensteinHexadPairPoint_mem p)
    (eisensteinNineHexadPairOutside_mem p) d b hd hb (u⁻¹*t).toAdd he
  rw [eisensteinHexadPairSupport_pair,eisensteinHexadPairSupport_pair] at hpq
  have heq : q=p := Subtype.ext hpq
  subst q
  have hsign := eisensteinNineHexadFrame_phase_sign _ (eisensteinHexadPairSupport_mem p)
    _ _ (eisensteinHexadPairPoint_mem p) (eisensteinNineHexadPairOutside_mem p)
    d b hd hb (u⁻¹*t).toAdd he
  exact hbd hsign.symm

end Atlas.Conway

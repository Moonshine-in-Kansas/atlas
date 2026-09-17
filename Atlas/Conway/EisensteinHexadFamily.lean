import Atlas.Conway.EisensteinHexadPhaseDisjoint

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

local instance : MulAction (Multiplicative ternaryGolay) EisensteinFrame :=
  MulAction.compHom EisensteinFrame eisensteinPhaseIsometries

def eisensteinHexadPairSupport (p : TernaryConstantHexadPair) : Finset (Fin 12) :=
  (Finset.mem_image.mp p.property).choose

theorem eisensteinHexadPairSupport_mem (p : TernaryConstantHexadPair) :
    eisensteinHexadPairSupport p ∈ ternaryConstantHexads :=
  (Finset.mem_image.mp p.property).choose_spec.1

theorem eisensteinHexadPairSupport_pair (p : TernaryConstantHexadPair) :
    ternaryConstantHexadPair (eisensteinHexadPairSupport p)=p.val :=
  (Finset.mem_image.mp p.property).choose_spec.2

def eisensteinHexadPairPoint (p : TernaryConstantHexadPair) : Fin 12 :=
  (Finset.card_pos.mp (show 0<(eisensteinHexadPairSupport p).card by
    rw [((mem_ternaryConstantHexads _).mp (eisensteinHexadPairSupport_mem p)).1]; decide)).choose

theorem eisensteinHexadPairPoint_mem (p : TernaryConstantHexadPair) :
    eisensteinHexadPairPoint p ∈ eisensteinHexadPairSupport p :=
  (Finset.card_pos.mp (show 0<(eisensteinHexadPairSupport p).card by
    rw [((mem_ternaryConstantHexads _).mp (eisensteinHexadPairSupport_mem p)).1]; decide)).choose_spec

def eisensteinHexadPairFrame (p : TernaryConstantHexadPair) : EisensteinFrame :=
  eisensteinHexadFrame _ (eisensteinHexadPairSupport_mem p) _ (eisensteinHexadPairPoint_mem p)

def eisensteinHexadPairOrbit (p : TernaryConstantHexadPair) : Finset EisensteinFrame :=
  (Set.toFinite (MulAction.orbit (Multiplicative ternaryGolay) (eisensteinHexadPairFrame p))).toFinset

theorem eisensteinHexadPairOrbit_mem (p : TernaryConstantHexadPair) (F : EisensteinFrame) :
    F ∈ eisensteinHexadPairOrbit p ↔ ∃ t : Multiplicative ternaryGolay,
      eisensteinPhaseIsometries t • eisensteinHexadPairFrame p=F := by
  simp only [eisensteinHexadPairOrbit,Set.Finite.mem_toFinset]
  rfl

theorem eisensteinHexadPairOrbit_card (p : TernaryConstantHexadPair) :
    (eisensteinHexadPairOrbit p).card=81 := by
  have hc := eisensteinHexadPhaseOrbit_card _ (eisensteinHexadPairSupport_mem p)
    _ (eisensteinHexadPairPoint_mem p)
  change Nat.card (MulAction.orbit (Multiplicative ternaryGolay) (eisensteinHexadPairFrame p))=81 at hc
  rw [Nat.card_coe_set_eq] at hc
  unfold eisensteinHexadPairOrbit
  rw [← Set.ncard_eq_toFinset_card]
  exact hc

theorem eisensteinHexadPairOrbit_disjoint (p q : TernaryConstantHexadPair) (hpq : p≠q) :
    Disjoint (eisensteinHexadPairOrbit p) (eisensteinHexadPairOrbit q) := by
  apply Finset.disjoint_left.mpr
  intro F hF hG
  obtain ⟨t,ht⟩ := (eisensteinHexadPairOrbit_mem p F).mp hF
  obtain ⟨u,hu⟩ := (eisensteinHexadPairOrbit_mem q F).mp hG
  have he : eisensteinPhaseIsometries (u⁻¹*t) • eisensteinHexadPairFrame p=eisensteinHexadPairFrame q := by
    rw [map_mul,mul_smul,ht,← hu,← mul_smul,← map_mul,inv_mul_cancel,map_one,one_smul]
  have hp := eisensteinHexadFrame_phase_pair _ _ (eisensteinHexadPairSupport_mem p)
    (eisensteinHexadPairSupport_mem q) _ _ (eisensteinHexadPairPoint_mem p)
    (eisensteinHexadPairPoint_mem q) (u⁻¹*t).toAdd he
  rw [eisensteinHexadPairSupport_pair,eisensteinHexadPairSupport_pair] at hp
  exact hpq (Subtype.ext hp)

/-- The intrinsic family parametrized by complementary constant hexads and their code phases. -/
def eisensteinHexadFamily : Finset EisensteinFrame :=
  Finset.univ.biUnion eisensteinHexadPairOrbit

theorem eisensteinHexadFamily_card : eisensteinHexadFamily.card=891 := by
  rw [eisensteinHexadFamily,Finset.card_biUnion]
  · simp only [eisensteinHexadPairOrbit_card,Finset.sum_const,Finset.card_univ,
      Fintype.card_coe,ternaryConstantHexadPairs_card,nsmul_eq_mul]
    norm_num
  · intro p hp q hq hpq
    exact eisensteinHexadPairOrbit_disjoint p q hpq

end Atlas.Conway

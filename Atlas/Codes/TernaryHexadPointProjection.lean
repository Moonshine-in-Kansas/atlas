import Atlas.Codes.TernaryHexadProjection
import Atlas.Codes.TernarySupportedHexad

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Codes

def ternaryHexadPointProjection (c : TernarySixWords) (j : Fin 12) :
    ternaryGolay → (ternaryHexadFunctional c).ker × ZMod 3 :=
  fun t => (⟨fun i => t.val i.val,ternaryHexadRestriction_le c ⟨t,rfl⟩⟩,t.val j)

theorem ternaryHexadPointProjection_injective (c : TernarySixWords) (j : Fin 12)
    (hj : j ∉ ternarySupport c.val.val) : Function.Injective (ternaryHexadPointProjection c j) := by
  intro t u h
  have hS : ∀ i ∈ ternarySupport c.val.val,(t-u).val i=0 := by
    intro i hi
    have he := congrArg (fun z : (ternaryHexadFunctional c).ker × ZMod 3 => z.1.val ⟨i,hi⟩) h
    change t.val i=u.val i at he
    change t.val i-u.val i=0
    exact sub_eq_zero.mpr he
  have hj0 : (t-u).val j=0 := by
    have he := congrArg Prod.snd h
    exact sub_eq_zero.mpr he
  have hz := ternaryGolay_constant_hexad_point c (t-u) 0 hS j hj hj0
  apply Subtype.ext
  funext i
  exact sub_eq_zero.mp (hz i)

theorem ternaryHexadPointProjection_bijective (c : TernarySixWords) (j : Fin 12)
    (hj : j ∉ ternarySupport c.val.val) : Function.Bijective (ternaryHexadPointProjection c j) := by
  classical
  letI := Fintype.ofFinite ternaryGolay
  letI := Fintype.ofFinite ((ternaryHexadFunctional c).ker × ZMod 3)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨ternaryHexadPointProjection_injective c j hj,?_⟩
  have ht : Nat.card ((ternaryHexadFunctional c).ker × ZMod 3)=729 := by
    rw [Nat.card_prod,ternaryHexadPhase_card]
    norm_num
  have hs : Nat.card ternaryGolay=729 := ternaryGolay_card
  exact Nat.card_eq_fintype_card.symm.trans (hs.trans (ht.symm.trans Nat.card_eq_fintype_card))

/-- Arbitrary orthogonal phases on a hexad and an independent phase at one
outside point extend uniquely to an actual codeword. -/
theorem ternaryHexadPointPhase_lift (c : TernarySixWords) (j : Fin 12)
    (hj : j ∉ ternarySupport c.val.val) (a : (ternaryHexadFunctional c).ker) (b : ZMod 3) :
    ∃ t : ternaryGolay,(∀ i : ternarySupport c.val.val,t.val i.val=a.val i) ∧ t.val j=b := by
  obtain ⟨t,ht⟩ := (ternaryHexadPointProjection_bijective c j hj).surjective (a,b)
  exact ⟨t,fun i => congrArg (fun z : (ternaryHexadFunctional c).ker × ZMod 3 => z.1.val i) ht,
    congrArg Prod.snd ht⟩

end Atlas.Codes

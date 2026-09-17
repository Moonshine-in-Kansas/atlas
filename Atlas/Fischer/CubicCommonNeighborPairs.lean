import Atlas.Fischer.CubicCommonNeighborResidual
import Atlas.Fischer.CountingSupportFibres

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev CubicCommonPairParameters (i j k : Fin 6) :=
  Σ l : CubicResidualColumn i j k,
    {t : CountingSourceTypeB // countingHexSupport t.1.val={i,j,k,l.val}}

def cubicSourceCommonTwoMap (i j k : Fin 6) (t : CubicCommonPairParameters i j k) :
    CubicSourceCommonNeighbors i j k 2 :=
  ⟨.inr (.inl t.2.val),(cubicSourceCommonCondition_B i j k 2 _).mpr ⟨rfl,by
    have h : i ∈ countingHexSupport t.2.val.1.val := by rw [t.2.property]; simp
    simpa [countingHexSupport] using h,by
    have h : j ∈ countingHexSupport t.2.val.1.val := by rw [t.2.property]; simp
    simpa [countingHexSupport] using h,by
    have h : k ∈ countingHexSupport t.2.val.1.val := by rw [t.2.property]; simp
    simpa [countingHexSupport] using h⟩⟩

def cubicSourceCommonTwoEquiv (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    CubicCommonPairParameters i j k ≃ CubicSourceCommonNeighbors i j k 2 :=
  Equiv.ofBijective (cubicSourceCommonTwoMap i j k) (by
    constructor
    · rintro ⟨l,a⟩ ⟨m,b⟩ h
      have hb : a.val=b.val := Sum.inl.inj (Sum.inr.inj (congrArg Subtype.val h))
      have hs : ({i,j,k,l.val} : Finset (Fin 6))={i,j,k,m.val} :=
        a.property.symm.trans ((congrArg (fun t : CountingSourceTypeB => countingHexSupport t.1.val) hb).trans b.property)
      have hm : l.val ∈ ({i,j,k,m.val} : Finset (Fin 6)) := by rw [← hs]; simp
      have hlm : l=m := Subtype.ext (by simpa [l.property.1,l.property.2.1,l.property.2.2] using hm)
      subst m
      exact congrArg (fun z => Sigma.mk l z) (Subtype.ext hb)
    · rintro ⟨a | (b | c),h⟩
      · rcases (cubicSourceCommonCondition_A i j k 2 a).mp h with h | h <;> omega
      · have hh := (cubicSourceCommonCondition_B i j k 2 b).mp h
        have hs : (countingHexSupport b.1.val).card=4 :=
          (countingHexSupport_card b.1.val).trans b.1.property
        have hi : i ∈ countingHexSupport b.1.val := by simpa [countingHexSupport] using hh.2.1
        have hj : j ∈ countingHexSupport b.1.val := by simpa [countingHexSupport] using hh.2.2.1
        have hk : k ∈ countingHexSupport b.1.val := by simpa [countingHexSupport] using hh.2.2.2
        obtain ⟨l,hl⟩ := cubicCommonNeighbor_four_completion _ hs i j k hij hik hjk hi hj hk
        exact ⟨⟨l,b,hl⟩,rfl⟩
      · have hh := (cubicSourceCommonCondition_C i j k 2 c hij hik hjk).mp h
        omega)

theorem cubicSourceCommonTwo_card (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nat.card (CubicSourceCommonNeighbors i j k 2)=72 := by
  rw [← Nat.card_congr (cubicSourceCommonTwoEquiv i j k hij hik hjk),Nat.card_sigma]
  have he (l : CubicResidualColumn i j k) :
      Nat.card {t : CountingSourceTypeB // countingHexSupport t.1.val={i,j,k,l.val}}=24 := by
    apply countingSourceTypeB_support_card
    simp [hij,hik,hjk,Ne.symm l.property.1,Ne.symm l.property.2.1,Ne.symm l.property.2.2]
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [← Nat.card_eq_fintype_card,cubicResidualColumn_card i j k hij hik hjk]

end Atlas.Fischer

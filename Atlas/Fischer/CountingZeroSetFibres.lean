import Atlas.Fischer.CountingSupportFibres

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Zero columns in an actual word of the source hexacode. -/
def countingHexZeroSet (h : countingHexacode) : Finset (Fin 6) := (countingHexSupport h)ᶜ

theorem countingHexZeroSet_mem (h : countingHexacode) (i : Fin 6) :
    i ∈ countingHexZeroSet h ↔ h.val i=0 := by simp [countingHexZeroSet,countingHexSupport]

theorem countingHexZeroSet_card (h : countingHexacode) :
    (countingHexZeroSet h).card+hammingNorm h.val=6 := by
  rw [countingHexZeroSet,Finset.card_compl,countingHexSupport_card]
  have hm : hammingNorm h.val≤6 := by
    change (Finset.univ.filter (fun i : Fin 6 => h.val i≠0)).card≤6
    exact (Finset.card_filter_le _ _).trans (by simp)
  simp only [Fintype.card_fin]
  omega

theorem countingHexZeroSet_univ_iff (h : countingHexacode) :
    countingHexZeroSet h=Finset.univ ↔ h=0 := by
  constructor
  · intro hh
    apply Subtype.ext
    funext i
    exact (countingHexZeroSet_mem h i).mp (by rw [hh]; simp)
  · rintro rfl
    ext i
    simp [countingHexZeroSet_mem]

theorem countingHexZeroSet_empty_iff (h : countingHexacode) :
    countingHexZeroSet h=∅ ↔ hammingNorm h.val=6 := by
  have hc := countingHexZeroSet_card h
  rw [← Finset.card_eq_zero]
  omega

theorem countingHexZeroSet_two_fiber_card (Z : Finset (Fin 6)) (hZ : Z.card=2) :
    Nat.card {h : countingHexacode // countingHexZeroSet h=Z}=3 := by
  have he : ∀ h : countingHexacode, countingHexZeroSet h=Z ↔ countingHexSupport h=Zᶜ := by
    intro h
    constructor
    · intro hh
      simpa [countingHexZeroSet] using congrArg (fun Z : Finset (Fin 6) => Zᶜ) hh
    · intro hh
      simp [countingHexZeroSet,hh]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  apply countingHexSupport_fiber_card
  rw [Finset.card_compl,hZ]
  decide

theorem countingHexZeroSet_univ_fiber_card :
    Nat.card {h : countingHexacode // countingHexZeroSet h=Finset.univ}=1 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight countingHexZeroSet_univ_iff)]
  simp

theorem countingHexZeroSet_empty_fiber_card :
    Nat.card {h : countingHexacode // countingHexZeroSet h=∅}=18 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight countingHexZeroSet_empty_iff),
    countingHexacode_weight_distribution]
  decide

/-- These are all zero-set types; this is inherited from the actual code weights. -/
theorem countingHexZeroSet_cases (h : countingHexacode) :
    countingHexZeroSet h=Finset.univ ∨ (countingHexZeroSet h).card=2 ∨ countingHexZeroSet h=∅ := by
  have hc := countingHexZeroSet_card h
  rcases countingHexacode_weights h with hh | hh | hh
  · left
    exact Finset.eq_univ_of_card _ (by simpa [hh] using hc)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr ((countingHexZeroSet_empty_iff h).mpr hh))

/-- Full zero-set fiber cardinality, including all impossible patterns. -/
theorem countingHexZeroSet_fiber_card (Z : Finset (Fin 6)) :
    Nat.card {h : countingHexacode // countingHexZeroSet h=Z}=
      (if Z=Finset.univ then 1 else 0)+(if Z.card=2 then 3 else 0)+
        (if Z=∅ then 18 else 0) := by
  by_cases hu : Z=Finset.univ
  · subst Z
    simpa [show (Finset.univ : Finset (Fin 6))≠∅ by decide] using countingHexZeroSet_univ_fiber_card
  by_cases h2 : Z.card=2
  · have hn : Z≠∅ := by intro hz; simpa [hz] using h2
    simpa [hu,h2,hn] using countingHexZeroSet_two_fiber_card Z h2
  by_cases hz : Z=∅
  · subst Z
    simpa [show (∅ : Finset (Fin 6))≠Finset.univ by decide] using countingHexZeroSet_empty_fiber_card
  have hi : IsEmpty {h : countingHexacode // countingHexZeroSet h=Z} := ⟨by
    rintro ⟨h,hh⟩
    rcases countingHexZeroSet_cases h with he | he | he
    · exact hu (hh.symm.trans he)
    · exact h2 (hh ▸ he)
    · exact hz (hh.symm.trans he)⟩
  simp [hu,h2,hz]

/-- Arbitrary weights can be summed over the exact zero-set fibers. -/
theorem countingHexZeroSet_weighted_sum (f : Finset (Fin 6) → ℕ) :
    (∑ h : countingHexacode, f (countingHexZeroSet h))=
      ∑ Z : Finset (Fin 6),
        ((if Z=Finset.univ then 1 else 0)+(if Z.card=2 then 3 else 0)+
          (if Z=∅ then 18 else 0))*f Z := by
  rw [← Fintype.sum_fiberwise' countingHexZeroSet f]
  apply Finset.sum_congr rfl
  intro Z _
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,
    countingHexZeroSet_fiber_card]
  simp

/-- The source zero-set table, as an exact weighted sum identity. -/
theorem countingHexZeroSet_sum (f : Finset (Fin 6) → ℕ) :
    (∑ h : countingHexacode, f (countingHexZeroSet h))=
      f Finset.univ+(∑ Z ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2, 3*f Z)+18*f ∅ := by
  rw [countingHexZeroSet_weighted_sum]
  simp_rw [add_mul,ite_mul,zero_mul,one_mul]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have he : (Finset.univ : Finset (Finset (Fin 6))).filter (fun Z => Z.card=2)=
      (Finset.univ : Finset (Fin 6)).powersetCard 2 := by
    ext Z
    simp
  rw [← Finset.sum_filter,he]

end Atlas.Fischer



import Atlas.Fischer.CountingSourceShapes

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def countingSourceShapeFiberA (a : CountingSourceTypeA) :
    {t : CountingSourceParameters // countingSourceShape t=.inl a} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨.inl a,rfl⟩
  left_inv := by
    rintro ⟨t,ht⟩
    apply Subtype.ext
    rcases t with b | (b | c)
    · exact congrArg Sum.inl (Sum.inl.inj ht).symm
    · cases ht
    · cases ht
  right_inv := by intro x; cases x; rfl

def countingSourceShapeFiberB (S : {S : Finset (Fin 6) // S.card=4}) :
    {t : CountingSourceParameters // countingSourceShape t=.inr (.inl S)} ≃
      {t : CountingSourceTypeB // countingHexSupport t.1.val=S.val} where
  toFun := by
    rintro ⟨t,ht⟩
    rcases t with a | (b | c)
    · cases ht
    · exact ⟨b,congrArg Subtype.val (Sum.inl.inj (Sum.inr.inj ht))⟩
    · cases ht
  invFun t := ⟨.inr (.inl t.val),congrArg (fun s => Sum.inr (Sum.inl s))
      (Subtype.ext t.property)⟩
  left_inv := by
    rintro ⟨t,ht⟩
    rcases t with a | (b | c)
    · cases ht
    · rfl
    · cases ht
  right_inv := by intro t; rfl

def countingSourceShapeFiberC (j : Fin 6) :
    {t : CountingSourceParameters // countingSourceShape t=.inr (.inr j)} ≃ countingHexacode where
  toFun := by
    rintro ⟨t,ht⟩
    rcases t with a | (b | c)
    · cases ht
    · cases ht
    · exact c.1
  invFun h := ⟨.inr (.inr (h,j)),rfl⟩
  left_inv := by
    rintro ⟨t,ht⟩
    apply Subtype.ext
    rcases t with a | (b | c)
    · cases ht
    · cases ht
    · have he : c.2=j := Sum.inr.inj (Sum.inr.inj ht)
      exact congrArg (fun v : CountingSourceTypeC =>
        (Sum.inr (Sum.inr v) : CountingSourceParameters)) (Prod.ext rfl he.symm)
  right_inv := by intro h; rfl

/-- The actual parameter fibers over geometric profiles have sizes1,24,64.
The latter two are derived from the retained hexacode and even-mask proofs. -/
theorem countingSourceShape_fiber_card (s : CountingSourceShape) :
    Nat.card {t : CountingSourceParameters // countingSourceShape t=s} =
      countingShapeMultiplicity s := by
  rcases s with a | (b | c)
  · rw [Nat.card_congr (countingSourceShapeFiberA a)]
    simp [countingShapeMultiplicity]
  · rw [Nat.card_congr (countingSourceShapeFiberB b)]
    exact countingSourceTypeB_support_card b.val b.property
  · rw [Nat.card_congr (countingSourceShapeFiberC c)]
    exact countingHexacode_card

end Atlas.Fischer

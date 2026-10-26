import Atlas.LinearAlgebra.DoubledCoordinates

/-! Cardinal invariants of doubling under additive equivalence. -/
namespace Atlas.LinearAlgebra

noncomputable def doubledAddEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃+ N) : Doubled M ≃ Doubled N where
  toFun x := ⟨e x.val,by obtain ⟨y,hy⟩ := x.prop; exact ⟨e y,by rw [← map_nsmul,hy]⟩⟩
  invFun x := ⟨e.symm x.val,by obtain ⟨y,hy⟩ := x.prop; exact ⟨e.symm y,by rw [← map_nsmul,hy]⟩⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)

noncomputable def doubledProdEquiv (M N : Type*) [AddCommGroup M] [AddCommGroup N] :
    Doubled (M×N) ≃ Doubled M × Doubled N where
  toFun x := (⟨x.val.1,by obtain ⟨y,hy⟩ := x.prop; exact ⟨y.1,congrArg Prod.fst hy⟩⟩,
    ⟨x.val.2,by obtain ⟨y,hy⟩ := x.prop; exact ⟨y.2,congrArg Prod.snd hy⟩⟩)
  invFun x := ⟨(x.1.val,x.2.val),by
    obtain ⟨a,ha⟩ := x.1.prop
    obtain ⟨b,hb⟩ := x.2.prop
    exact ⟨(a,b),Prod.ext ha hb⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def doubledPiEquiv (ι M : Type*) [AddCommGroup M] :
    Doubled (ι→M) ≃ (ι→Doubled M) where
  toFun x i := ⟨x.val i,by obtain ⟨y,hy⟩ := x.prop; exact ⟨y i,congrFun hy i⟩⟩
  invFun x := ⟨fun i => (x i).val,by
    choose y hy using fun i => (x i).prop
    exact ⟨y,funext hy⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem doubled_zmod_two_card : Nat.card (Doubled (ZMod 2))=1 := by
  change Nat.card {x : ZMod 2 // ∃ y : ZMod 2, (2 : ℕ) • y=x}=1
  rw [Nat.card_eq_fintype_card]
  decide

theorem doubled_four_two_card (m n : ℕ) :
    Nat.card (Doubled ((Fin m→ZMod 4)×(Fin n→ZMod 2)))=2^m := by
  rw [Nat.card_congr (doubledProdEquiv _ _),Nat.card_prod,
    Nat.card_congr (doubledPiEquiv (Fin m) (ZMod 4)),
    Nat.card_congr (doubledPiEquiv (Fin n) (ZMod 2))]
  simp [Nat.card_fun,doubled_zmod_four_card,doubled_zmod_two_card]

end Atlas.LinearAlgebra

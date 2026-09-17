import Atlas.Fischer.ParkerTripleRadical

namespace Atlas.Fischer
open Atlas.Codes

/-- The actual center of the nonassociative Parker multiplication: commuting
with every element and belonging to all three nuclei. -/
def IsParkerCentral (x : ParkerLoop) : Prop :=
  (∀ y, parkerLoopMultiply x y=parkerLoopMultiply y x) ∧
  (∀ y z, parkerLoopMultiply (parkerLoopMultiply x y) z=
    parkerLoopMultiply x (parkerLoopMultiply y z)) ∧
  (∀ y z, parkerLoopMultiply (parkerLoopMultiply y x) z=
    parkerLoopMultiply y (parkerLoopMultiply x z)) ∧
  (∀ y z, parkerLoopMultiply (parkerLoopMultiply y z) x=
    parkerLoopMultiply y (parkerLoopMultiply z x))

theorem parkerSign_eq_self_iff (s : Bit) (x : ParkerLoop) : parkerSign s x=x ↔ s=0 := by
  constructor
  · intro h
    have he := congrArg Prod.snd h
    change x.2+s=x.2 at he
    exact add_left_cancel (he.trans (add_zero x.2).symm)
  · rintro rfl
    exact parkerSign_zero x

theorem parkerCentral_one : IsParkerCentral (0,0) := by
  simp [IsParkerCentral,parkerLoopMultiply_one_left,parkerLoopMultiply_one_right]

theorem parkerCentral_omega : IsParkerCentral parkerOmega :=
  ⟨parkerOmega_commutes,parkerOmega_associates_left,
    parkerOmega_associates_middle,parkerOmega_associates_right⟩

theorem parkerCentral_sign (x : ParkerLoop) (hx : IsParkerCentral x) (s : Bit) :
    IsParkerCentral (parkerSign s x) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro y
    rw [parkerLoopMultiply_sign_left,parkerLoopMultiply_sign_right,hx.1]
  · intro y z
    rw [parkerLoopMultiply_sign_left,parkerLoopMultiply_sign_left,
      parkerLoopMultiply_sign_left,hx.2.1]
  · intro y z
    rw [parkerLoopMultiply_sign_right,parkerLoopMultiply_sign_left,
      parkerLoopMultiply_sign_left,parkerLoopMultiply_sign_right,hx.2.2.1]
  · intro y z
    rw [parkerLoopMultiply_sign_right,parkerLoopMultiply_sign_right,
      parkerLoopMultiply_sign_right,hx.2.2.2]

/-- Exact full-center criterion for the actual marked Parker loop. -/
theorem parkerCentral_iff (x : ParkerLoop) :
    IsParkerCentral x ↔ x.1=0 ∨ x.1=golayOne := by
  constructor
  · intro hx
    apply (parkerTripleIntersection_radical x.1).mp
    intro b c
    have h := hx.2.1 (b,0) (c,0)
    rw [parkerLoopMultiply_associator] at h
    exact (parkerSign_eq_self_iff _ _).mp h
  · intro h
    rcases x with ⟨a,s⟩
    change a=0 ∨ a=golayOne at h
    rcases h with rfl | rfl
    · simpa only [parkerSign,zero_add] using parkerCentral_sign (0,0) parkerCentral_one s
    · simpa only [parkerSign,parkerOmega,zero_add] using parkerCentral_sign parkerOmega parkerCentral_omega s

/-- The center consists exactly of the two signs and the two signed copies
of the distinguished all-ones loop element. -/
theorem parkerCentral_four_forms (x : ParkerLoop) :
    IsParkerCentral x ↔ ∃ s : Bit, x=(0,s) ∨ x=parkerSign s parkerOmega := by
  rw [parkerCentral_iff]
  constructor
  · rintro (h | h)
    · exact ⟨x.2,Or.inl (Prod.ext h rfl)⟩
    · exact ⟨x.2,Or.inr (Prod.ext h (zero_add x.2).symm)⟩
  · rintro ⟨s,rfl | rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl


/-- The two possible central code coordinates are distinct. -/
theorem parkerGolayOne_ne_zero : golayOne ≠ 0 := by
  intro h
  have he := congrArg (fun a : golay => a.val (0,0)) h
  exact one_ne_zero he

/-- The center has exactly four elements, counted structurally by its code
coordinate and its independent sign. -/
theorem parkerCenter_card : Nat.card {x : ParkerLoop // IsParkerCentral x}=4 := by
  let A := {a : golay // a=0 ∨ a=golayOne}
  have hA : Nat.card A=2 := by
    apply Nat.card_eq_two_iff.mpr
    refine ⟨⟨0,Or.inl rfl⟩,⟨golayOne,Or.inr rfl⟩,?_,?_⟩
    · intro h
      exact parkerGolayOne_ne_zero (congrArg Subtype.val h).symm
    · ext a
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_univ,iff_true]
      rcases a.prop with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  let e : {x : ParkerLoop // IsParkerCentral x} ≃ A × Bit := {
    toFun := fun x => (⟨x.val.1,(parkerCentral_iff x.val).mp x.prop⟩,x.val.2)
    invFun := fun p => ⟨(p.1.val,p.2),(parkerCentral_iff _).mpr p.1.prop⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_prod,hA]
  norm_num [Bit,Nat.card_eq_fintype_card]

end Atlas.Fischer

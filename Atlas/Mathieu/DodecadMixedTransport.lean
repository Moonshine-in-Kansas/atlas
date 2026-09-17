import Atlas.Mathieu.DodecadMixedNoFixedPoint
import Atlas.Mathieu.Mathieu11Simplicity
import Atlas.Mathieu.Mathieu12Choice
import Atlas.GroupTheory.SimpleSmallAction

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

abbrev DodecadExterior (D : Dodecad) := {b : Omega // b ∉ D.val}

instance dodecadExteriorAction (D : Dodecad) : MulAction (Mathieu12DodecadModel D) (DodecadExterior D) where
  smul g b := ⟨g.val.val b.val,by
    have hg : permuteBlock g.val.val D.val = D.val := congrArg Subtype.val g.prop
    intro hb
    exact b.prop ((permuteBlock_apply_mem g.val.val D.val b.val).mp (hg.symm ▸ hb))⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

theorem dodecadExterior_card (D : Dodecad) : Nat.card (DodecadExterior D) = 12 := by
  let e : DodecadExterior D ≃ {b // b ∈ D.valᶜ} :=
    Equiv.subtypeEquivRight (fun b => by simp)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe,Finset.card_compl,
    dodecad_size D.val D.prop]
  norm_num [Omega,HexIndex]

theorem mathieu11_exterior_transitive (D : Dodecad) (a : Mathieu12Points D) :
    MulAction.IsPretransitive (Mathieu11PointModel D a) (DodecadExterior D) := by
  letI := mathieu11_simple D a
  apply Atlas.GroupTheory.simple_small_action_pretransitive (Mathieu11PointModel D a)
    (DodecadExterior D) 11 (by decide)
  · rw [mathieu11_order]; decide
  · rw [dodecadExterior_card]; decide
  · intro b
    obtain ⟨g,hg,hga,hgb⟩ := dodecad_inside_point_moves_outside D a.val b.val a.prop b.prop
    let g12 : Mathieu12DodecadModel D := ⟨g,Subtype.ext hg⟩
    let g11 : Mathieu11PointModel D a := ⟨g12,Subtype.ext hga⟩
    exact ⟨g11,fun he => hgb (congrArg Subtype.val he)⟩

theorem dodecad_mixed_flags_transitive (D E : Dodecad) (a b c d : Omega)
    (ha : a ∈ D.val) (hb : b ∉ D.val) (hc : c ∈ E.val) (hd : d ∉ E.val) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val D.val = E.val ∧ g.val a = c ∧ g.val b = d := by
  obtain ⟨q,hq,hqa⟩ := dodecad_point_flags_transitive D E ⟨a,ha⟩ ⟨c,hc⟩
  have hqD : permuteBlock q.val D.val = E.val := congrArg Subtype.val hq
  have hqb : q.val b ∉ E.val := by
    rw [← hqD]
    exact fun hm => hb ((permuteBlock_apply_mem q.val D.val b).mp hm)
  let c' : Mathieu12Points E := ⟨c,hc⟩
  letI := mathieu11_exterior_transitive E c'
  obtain ⟨h,hh⟩ := MulAction.exists_smul_eq (Mathieu11PointModel E c')
    (⟨q.val b,hqb⟩ : DodecadExterior E) ⟨d,hd⟩
  have hhD : permuteBlock h.val.val.val E.val = E.val := congrArg Subtype.val h.val.prop
  have hhc : h.val.val.val c = c := congrArg Subtype.val h.prop
  have hhb : h.val.val.val (q.val b) = d := congrArg Subtype.val hh
  refine ⟨h.val.val*q,?_,?_,?_⟩
  · change permuteBlock (h.val.val.val*q.val) D.val = E.val
    rw [permuteBlock_mul,hqD,hhD]
  · change h.val.val.val (q.val a) = c
    rw [hqa,hhc]
  · exact hhb

end Atlas.Codes

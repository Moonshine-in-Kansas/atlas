import Atlas.Mathieu.DodecadFlags
import Atlas.Mathieu.Mathieu24Order

noncomputable section
namespace Atlas.Codes

instance dodecadMulAction : MulAction Mathieu24CodeModel Dodecad where
  smul g D := ⟨permuteBlock g.val D.val,codePreserving_dodecad_forward _ g.prop _ D.prop⟩
  one_smul D := Subtype.ext (permuteBlock_one D.val)
  mul_smul g h D := Subtype.ext (permuteBlock_mul g.val h.val D.val)

theorem dodecad_action_transitive : MulAction.IsPretransitive Mathieu24CodeModel Dodecad := by
  constructor
  intro D E
  obtain ⟨g,hg⟩ := dodecad_transitive_explicit D E
  exact ⟨g,Subtype.ext hg⟩

abbrev Mathieu12DodecadModel (D : Dodecad) := MulAction.stabilizer Mathieu24CodeModel D
abbrev Mathieu12Points (D : Dodecad) := {x : Omega // x ∈ D.val}

theorem mathieu12_degree (D : Dodecad) : Nat.card (Mathieu12Points D) = 12 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  exact dodecad_size D.val D.prop

def dodecadOrbitEquiv (D : Dodecad) : MulAction.orbit Mathieu24CodeModel D ≃ Dodecad where
  toFun x := x.val
  invFun E := ⟨E,by
    obtain ⟨g,hg⟩ := dodecad_transitive_explicit D E
    exact MulAction.mem_orbit_iff.mpr ⟨g,Subtype.ext hg⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def dodecadOrbitStabilizerEquiv (D : Dodecad) :
    Dodecad × Mathieu12DodecadModel D ≃ Mathieu24CodeModel :=
  ((dodecadOrbitEquiv D).symm.prodCongr (Equiv.refl _)).trans
    (MulAction.orbitProdStabilizerEquivGroup Mathieu24CodeModel D)

theorem dodecad_type_card : Nat.card Dodecad = 2576 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_coe,dodecads_card]

theorem mathieu12_orbit_order (D : Dodecad) :
    2576 * Nat.card (Mathieu12DodecadModel D) = Nat.card Mathieu24CodeModel := by
  rw [← Nat.card_congr (dodecadOrbitStabilizerEquiv D),Nat.card_prod,dodecad_type_card]

theorem mathieu12_order (D : Dodecad) : Nat.card (Mathieu12DodecadModel D) = 95040 := by
  have h := mathieu12_orbit_order D
  rw [mathieu24_order] at h
  omega

theorem mathieu12_order_factorization (D : Dodecad) :
    Nat.card (Mathieu12DodecadModel D) = 2^6 * 3^3 * 5 * 11 := by
  rw [mathieu12_order]
  rfl

theorem mathieu12_mem (D : Dodecad) (g : Mathieu24CodeModel) :
    g ∈ Mathieu12DodecadModel D ↔ permuteBlock g.val D.val = D.val := by
  change (g • D = D) ↔ _
  exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩

instance mathieu12MulAction (D : Dodecad) : MulAction (Mathieu12DodecadModel D) (Mathieu12Points D) where
  smul g x := ⟨g.val.val x.val, by
    have hg := (mathieu12_mem D g.val).mp g.prop
    have hm : g.val.val x.val ∈ permuteBlock g.val.val D.val :=
      Finset.mem_image.mpr ⟨x.val,x.prop,rfl⟩
    simpa only [hg] using hm⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem mathieu12_four_transitive (D : Dodecad) :
    MulAction.IsMultiplyPretransitive (Mathieu12DodecadModel D) (Mathieu12Points D) 4 := by
  apply MulAction.isMultiplyPretransitive_iff.mpr
  intro e f
  let e' := e.trans (Function.Embedding.subtype (fun x => x ∈ D.val))
  let f' := f.trans (Function.Embedding.subtype (fun x => x ∈ D.val))
  obtain ⟨g,hg,hgf⟩ := dodecad_ordered_flags_transitive D D e' f'
    (fun k => (e k).prop) (fun k => (f k).prop)
  refine ⟨⟨g,(mathieu12_mem D g).mpr hg⟩,?_⟩
  apply Function.Embedding.ext
  intro k
  exact Subtype.ext (hgf k)

def mathieu12_embedding (D : Dodecad) : Mathieu12DodecadModel D →* Mathieu24CodeModel :=
  (Mathieu12DodecadModel D).subtype

theorem mathieu12_embedding_injective (D : Dodecad) :
    Function.Injective (mathieu12_embedding D) := Subtype.val_injective

end Atlas.Codes

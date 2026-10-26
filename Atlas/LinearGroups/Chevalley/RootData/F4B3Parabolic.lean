import Atlas.LinearGroups.Chevalley.RootData.F4B3WordAction
import Atlas.LinearGroups.Chevalley.RootData.F4ShortParabolic
import Atlas.LinearGroups.Chevalley.RootData.ParabolicWeylEmbedding

/-! The actual B3 root-permutation Weyl image is exactly the zero-wall
parabolic of the F4 short-axis functional. Its length is the ambient F4
length. The required injective homomorphism is constructed from integer word
actions; neither equal orders nor an abstract Coxeter identification is used. -/
noncomputable section
namespace Atlas.Chevalley.F4B3
open Classical ClassicalData RootData F4Data

private def shortestWord (w : ClassicalBParabolic.W 2) : List (baseB 2).support :=
  (rootWeylLength_spec (pairingB 3) (baseB 2) w).choose

private theorem shortestWord_eval (w : ClassicalBParabolic.W 2) :
    rootWeylWord (pairingB 3) (baseB 2) (shortestWord w) = w := by
  apply Subtype.ext
  rw [rootWeylWord_val]
  exact (rootWeylLength_spec (pairingB 3) (baseB 2) w).choose_spec.2

def weylHom : ClassicalBParabolic.W 2 →* F4ShortOrbit.W where
  toFun w := markedWord (shortestWord w)
  map_one' := markedWord_eq_of_rootWord_eq (shortestWord 1) [] (shortestWord_eval 1)
  map_mul' w v := by
    have he : rootWeylWord (pairingB 3) (baseB 2) (shortestWord (w * v)) =
        rootWeylWord (pairingB 3) (baseB 2) (shortestWord w ++ shortestWord v) := by
      rw [rootWeylWord_append, shortestWord_eval, shortestWord_eval, shortestWord_eval]
    have h := markedWord_eq_of_rootWord_eq _ _ he
    simpa only [markedWord, List.map_append, rootWeylWord_append] using h

theorem weylHom_word (l : List (baseB 2).support) :
    weylHom (rootWeylWord (pairingB 3) (baseB 2) l) = markedWord l :=
  markedWord_eq_of_rootWord_eq _ l (shortestWord_eval _)

theorem weylHom_injective : Function.Injective weylHom := by
  intro w v h
  change markedWord (shortestWord w) = markedWord (shortestWord v) at h
  have he := rootWord_eq_of_markedWord_eq _ _ h
  simpa only [shortestWord_eval] using he

theorem weylHom_simple (i : (baseB 2).support) :
    weylHom (simpleWeylReflection (pairingB 3) (baseB 2) i) =
      simpleWeylReflection pairing base (markedSimple i) := by
  simpa only [rootWeylWord, markedWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one] using weylHom_word [i]

theorem markedSimple_mem (i : (baseB 2).support) : markedSimple i ∈ F4ShortOrbit.J := by
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
  intro he
  have hk := baseIndexEquiv.injective he
  have hv := congrArg Fin.val hk
  have hb := ((baseBIndexEquiv 2).symm i).isLt
  change ((baseBIndexEquiv 2).symm i).val = 3 at hv
  omega

theorem markedSimple_range (j : base.support) :
    j ∈ F4ShortOrbit.J ↔ ∃ i : (baseB 2).support, markedSimple i = j := by
  constructor
  · intro hj
    obtain ⟨k, rfl⟩ := baseIndexEquiv.surjective j
    have hk : k ≠ (3 : Fin 4) := by
      intro he
      exact (Finset.mem_erase.mp hj).1 (congrArg baseIndexEquiv he)
    have hkv : k.val ≠ 3 := fun h => hk (Fin.ext h)
    have hbound := k.isLt
    let a : Fin 3 := ⟨k.val, by omega⟩
    refine ⟨baseBIndexEquiv 2 a, ?_⟩
    simp only [markedSimple, Equiv.symm_apply_apply]
    apply congrArg baseIndexEquiv
    exact Fin.ext rfl
  · rintro ⟨i, rfl⟩
    exact markedSimple_mem i

theorem weylHom_range : weylHom.range = rootParabolicSubgroup pairing base F4ShortOrbit.J :=
  rootWeylHom_range_eq_parabolic (pairingB 3) (baseB 2) pairing base
    weylHom markedSimple weylHom_simple F4ShortOrbit.J markedSimple_range

def parabolicEquiv : ClassicalBParabolic.W 2 ≃*
    rootParabolicSubgroup pairing base F4ShortOrbit.J :=
  rootWeylHomParabolicEquiv (pairingB 3) (baseB 2) pairing base
    weylHom markedSimple weylHom_simple weylHom_injective F4ShortOrbit.J markedSimple_range

theorem parabolicEquiv_length (w : ClassicalBParabolic.W 2) :
    rootWeylLength pairing base (parabolicEquiv w).val =
      rootWeylLength (pairingB 3) (baseB 2) w :=
  rootWeylHomParabolicEquiv_length (pairingB 3) (baseB 2) pairing base
    weylHom markedSimple weylHom_simple weylHom_injective F4ShortOrbit.J markedSimple_range w

end Atlas.Chevalley.F4B3

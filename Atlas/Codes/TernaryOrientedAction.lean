import Atlas.Codes.TernaryOrientedTriads
import Atlas.Codes.TernarySyndromeAction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Codes

def ternaryOrientedMap (σ : Equiv.Perm (Fin 12)) (p : TernaryOrientedTriad) :
    TernaryOrientedTriad :=
  ⟨(p.val.1.map σ.toEmbedding, σ p.val.2), (mem_ternaryOrientedTriads _).mpr
    ⟨by rw [Finset.card_map]; exact ((mem_ternaryOrientedTriads _).mp p.property).1,
      Finset.mem_map.mpr ⟨p.val.2, ((mem_ternaryOrientedTriads _).mp p.property).2, rfl⟩⟩⟩

theorem ternaryOrientedMap_injective (σ : Equiv.Perm (Fin 12)) :
    Function.Injective (ternaryOrientedMap σ) := by
  intro p q h
  apply Subtype.ext
  have hs := congrArg (fun r : TernaryOrientedTriad => r.val.1) h
  have hi := congrArg (fun r : TernaryOrientedTriad => r.val.2) h
  exact Prod.ext (Finset.map_injective σ.toEmbedding hs) (σ.injective hi)

theorem ternaryOrientedMap_word (σ : Equiv.Perm (Fin 12)) (p : TernaryOrientedTriad) :
    ternaryOrientedWord (ternaryOrientedMap σ p).val =
      fun i => ternaryOrientedWord p.val (σ.symm i) := by
  funext i
  simp [ternaryOrientedWord, ternaryOrientedMap, ternaryTriadWord,
    Finset.mem_map_equiv, Pi.single_apply, Equiv.symm_apply_eq]

theorem ternaryOriented_embedding (p : TernaryOrientedTriad) :
    ∃ e : Fin 3 ↪ Fin 12, Finset.univ.map e = p.val.1 ∧ e 2 = p.val.2 := by
  have hp := (mem_ternaryOrientedTriads _).mp p.property
  let e₀ := (p.val.1.orderEmbOfFin hp.1).toEmbedding
  have hr : Finset.univ.map e₀ = p.val.1 := by
    simpa [e₀] using p.val.1.range_orderEmbOfFin hp.1
  have hm : p.val.2 ∈ Finset.univ.map e₀ := by rw [hr]; exact hp.2
  obtain ⟨k, _, hk⟩ := Finset.mem_map.mp hm
  let τ := Equiv.swap (2 : Fin 3) k
  refine ⟨τ.toEmbedding.trans e₀, ?_, ?_⟩
  · rw [← Finset.map_map]
    have ht : Finset.univ.map τ.toEmbedding = Finset.univ := by
      ext i
      simp
    rw [ht, hr]
  · change e₀ (Equiv.swap (2 : Fin 3) k 2) = p.val.2
    rw [Equiv.swap_apply_left]
    exact hk

/-- Actual M11 is transitive on the660 oriented triads, by its verified
three-transitivity, with the distinguished negative coordinate retained. -/
theorem ternaryOriented_transitive (p q : TernaryOrientedTriad) :
    ∃ g : TernaryPureAutomorphism, ternaryOrientedMap g.val p = q := by
  letI := ternaryPureAutomorphism_three_transitive
  obtain ⟨ep, hp, hip⟩ := ternaryOriented_embedding p
  obtain ⟨eq, hq, hiq⟩ := ternaryOriented_embedding q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq TernaryPureAutomorphism ep eq
  have he (i : Fin 3) : g.val (ep i) = eq i :=
    congrArg (fun e : Fin 3 ↪ Fin 12 => e i) hg
  refine ⟨g, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change p.val.1.map g.val.toEmbedding = q.val.1
    rw [← hp, ← hq, Finset.map_map]
    congr 1
  · change g.val p.val.2 = q.val.2
    rw [← hip, ← hiq]
    exact he 2

theorem ternaryOrientedRelated_map (g : TernaryPureAutomorphism) (p q : TernaryOrientedTriad) :
    ternaryOrientedRelated (ternaryOrientedMap g.val p).val (ternaryOrientedMap g.val q).val ↔
      ternaryOrientedRelated p.val q.val := by
  rw [ternaryOrientedRelated_iff, ternaryOrientedRelated_iff,
    ternaryOrientedMap_word, ternaryOrientedMap_word,
    ← ternarySyndromePermutation_class, ← ternarySyndromePermutation_class]
  exact (ternarySyndromePermutation g).injective.eq_iff

end Atlas.Codes

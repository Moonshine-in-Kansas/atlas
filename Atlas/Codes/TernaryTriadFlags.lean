import Atlas.Codes.TernaryGolayTriads

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Codes

theorem ternaryTriad_ordered_at (S : Finset (Fin 12)) (hS : S.card=3)
    (i : Fin 12) (hi : i ∈ S) :
    ∃ e : Fin 3 ↪ Fin 12, Finset.univ.map e=S ∧ e 0=i := by
  let e : Fin 3 ↪ Fin 12 := (S.orderEmbOfFin hS).toEmbedding
  have hr : Set.range e=(S : Set (Fin 12)) := by simpa [e] using S.range_orderEmbOfFin hS
  have hri : i ∈ Set.range e := by rw [hr]; exact hi
  obtain ⟨k,hk⟩ := hri
  refine ⟨(Equiv.swap 0 k).toEmbedding.trans e,?_,?_⟩
  · rw [← Finset.map_map]
    simp only [Finset.map_univ_equiv]
    simpa [e] using S.range_orderEmbOfFin hS
  · simpa using hk

/-- Three-transitivity supplies the marked-triad transitivity needed for heavy
positions, not just transitivity on unmarked supports. -/
theorem ternaryTriadFlags_transitive (S T : Finset (Fin 12))
    (hS : S.card=3) (hT : T.card=3) (i j : Fin 12) (hi : i ∈ S) (hj : j ∈ T) :
    ∃ g : TernaryPureAutomorphism,S.map g.val.toEmbedding=T ∧ g.val i=j := by
  letI := ternaryPureAutomorphism_three_transitive
  obtain ⟨e,he,hei⟩ := ternaryTriad_ordered_at S hS i hi
  obtain ⟨f,hf,hfj⟩ := ternaryTriad_ordered_at T hT j hj
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq TernaryPureAutomorphism e f
  have hh (k : Fin 3) : g.val (e k)=f k := congrArg (fun a : Fin 3 ↪ Fin 12 => a k) hg
  refine ⟨g,?_,?_⟩
  · rw [← he,Finset.map_map,← hf]
    congr 1
  · simpa only [hei,hfj] using hh 0

end Atlas.Codes

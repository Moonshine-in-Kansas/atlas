import Atlas.Sporadic.Janko1.WhitelawSRowsA
import Atlas.Sporadic.Janko1.WhitelawSRowsB
import Atlas.Sporadic.Janko1.WhitelawSRowsC

/-!
Uncompiled source-only endpoint. All eighty local rows are supplied by the
three predecessors, without an assumed S-closure premise. The actual group
orbit equality and action use the frozen structural reduction unchanged.
No group-order, stabilizer, sextic, primitivity or simplicity claim is made.
-/
noncomputable section
namespace Atlas.Janko1

theorem whitelaw_S_rows : ∀ (r : Fin 10) (a : SignParameters), WhitelawSRow r a := by
  intro r a
  obtain ⟨b, rfl⟩ := whitelawSearchSign_surjective a
  fin_cases r
  · exact whitelaw_S_seed_0 b
  · exact whitelaw_S_seed_1 b
  · exact whitelaw_S_seed_2 b
  · exact whitelaw_S_seed_3 b
  · exact whitelaw_S_seed_4 b
  · exact whitelaw_S_seed_5 b
  · exact whitelaw_S_seed_6 b
  · exact whitelaw_S_seed_7 b
  · exact whitelaw_S_seed_8 b
  · exact whitelaw_S_seed_9 b

theorem S_smul_mem_whitelawSet (p : ProjV) (hp : p ∈ whitelawSet) :
    S • p ∈ whitelawSet :=
  (S_preserves_whitelawSet_iff_rows.mpr whitelaw_S_rows) p hp

theorem S_smul_mem_whitelawSet_iff (p : ProjV) :
    S • p ∈ whitelawSet ↔ p ∈ whitelawSet := by
  constructor
  · intro hp
    simpa only [S_smul_S] using S_smul_mem_whitelawSet (S • p) hp
  · exact S_smul_mem_whitelawSet p

theorem generated_smul_mem_whitelawSet_iff (g : Model) (p : ProjV) :
    g • p ∈ whitelawSet ↔ p ∈ whitelawSet :=
  generated_smul_mem_whitelawSet_of_S S_smul_mem_whitelawSet g p

theorem generated_smul_mem_whitelawSet (g : Model) (p : ProjV)
    (hp : p ∈ whitelawSet) : g • p ∈ whitelawSet :=
  (generated_smul_mem_whitelawSet_iff g p).mpr hp

theorem whitelawSet_eq_generatedOrbit :
    whitelawSet = MulAction.orbit Model whitelawPoint :=
  whitelawSet_eq_generatedOrbit_iff_rows.mpr whitelaw_S_rows

/-- This is the actual point orbit cardinality, not the cardinality of G. -/
theorem card_generatedWhitelawOrbit :
    Nat.card (MulAction.orbit Model whitelawPoint) = 1596 := by
  rw [← whitelawSet_eq_generatedOrbit]
  exact card_whitelawPoints

instance whitelawModelAction : MulAction Model WhitelawPoints where
  smul g p := ⟨g • p.val, generated_smul_mem_whitelawSet g p.val p.property⟩
  one_smul p := Subtype.ext (one_smul Model p.val)
  mul_smul g h p := Subtype.ext (mul_smul g h p.val)

theorem whitelawModelAction_val (g : Model) (p : WhitelawPoints) :
    (g • p).val = g • p.val := rfl

theorem whitelawModelAction_H (h : H) (p : WhitelawPoints) :
    (⟨(h : G2.Model Field), H_le_generated h.property⟩ : Model) • p = h • p := by
  apply Subtype.ext
  rfl

theorem whitelawPoints_transitive : MulAction.IsPretransitive Model WhitelawPoints := by
  constructor
  intro p q
  obtain ⟨g, hg⟩ := whitelawSet_pair_transport p q
  exact ⟨g, Subtype.ext hg⟩

end Atlas.Janko1

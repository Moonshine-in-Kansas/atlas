import Atlas.Mathieu.Mathieu21LocalStabilizer
import Atlas.Mathieu.TetradTranslationOrder
import Atlas.GroupTheory.DegreeTwentyOneSimple
import Atlas.GroupTheory.NormalFormsTransport

noncomputable section
namespace Atlas.Codes
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

theorem mathieu21_simple (a : Omega) (b : Mathieu23Points a) (c : Mathieu22Points a b) :
    IsSimpleGroup (Mathieu21PointModel a b c) := by
  classical
  have := mathieu21_faithful a b c
  have := mathieu21_two_transitive a b c
  obtain ⟨d⟩ := (Nat.card_pos_iff.mp (show 0 < Nat.card (Mathieu21Points a b c) by
    rw [mathieu21_degree]; decide)).1
  let T := MulAction.stabilizer (Mathieu21PointModel a b c) d
  let e := mathieu21LocalEquiv a b c d (0,0)
  let U : Subgroup T := (tetradPointTranslations (0,0)).comap e.toMonoidHom
  have hu : Nat.card U = 16 := by
    exact (Atlas.GroupTheory.card_comap_equiv e _).trans (tetradPointTranslations_card (0,0))
  apply Atlas.GroupTheory.simple_degree_twenty_one d (mathieu21_degree a b c)
    (mathieu21_order a b c) U hu
  · exact Atlas.GroupTheory.normal_forms_transport e _
      (fun W hW => @tetradPoint_normal_subgroups (0,0) W hW)
  · exact Atlas.GroupTheory.no_injective_perm_transport e (Fin 8)
      (tetradPoint_no_injective_perm_eight (0,0))

end Atlas.Codes

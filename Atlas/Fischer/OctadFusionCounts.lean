import Atlas.Fischer.OctadMarkedOutsideMoments

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Exactly42 octads contain a prescribed interior point and exterior point
and meet the retained base octad in exactly two points. -/
theorem octad_fusion_count_one (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hS : S.card=1) (x : Omega) (hx : x∉O.val) :
    octadIntersectionCount O.val (insert x S) 2=42 := by
  have he := octad_marked_outside_equations O S hSO
    (Finset.card_pos.mp (by omega)) x hx 77 21
    (fun U hU => octadReplication_two U (by omega))
    (fun U hU => octadReplication_three U (by omega))
  rw [hS] at he
  norm_num at he
  omega

/-- Exactly6 octads contain a prescribed interior duad and exterior point
and meet the retained base octad in exactly that duad. -/
theorem octad_fusion_count_two (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hS : S.card=2) (x : Omega) (hx : x∉O.val) :
    octadIntersectionCount O.val (insert x S) 2=6 := by
  have he := octad_marked_outside_equations O S hSO
    (Finset.card_pos.mp (by omega)) x hx 21 5
    (fun U hU => octadReplication_three U (by omega))
    (fun U hU => octadReplication_four U (by omega))
  rw [hS] at he
  norm_num at he
  omega

/-- The full168/42/6 local fusion count, uniformly in the actual marked subset. -/
theorem octad_fusion_count (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hS : S.card≤2) (x : Omega) (hx : x∉O.val) :
    octadIntersectionCount O.val (insert x S) 2=
      if S.card=0 then 168 else if S.card=1 then 42 else 6 := by
  classical
  interval_cases hs : S.card
  · have hE := Finset.card_eq_zero.mp hs
    subst S
    simpa using (octad_outside_point_distribution O.val {x} O.prop
      (by simpa using hx) (by simp)).2.1
  · simpa using octad_fusion_count_one O S hSO hs x hx
  · simpa using octad_fusion_count_two O S hSO hs x hx

end Atlas.Fischer

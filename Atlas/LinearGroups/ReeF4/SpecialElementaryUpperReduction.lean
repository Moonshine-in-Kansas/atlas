import Atlas.LinearGroups.ReeF4.SpecialElementaryMiddleReduction

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem allowedCoordinateBound_negFour {R : Type*} [Zero R]
    (x : Fin 26 → R) (h7 : x 7 = 0) (h9 : x 9 = 0) (h24 : x 24 = 0) (h25 : x 25 = 0) :
    ∀ r, allowedSpecialLeadingRoot r → (-4 : ℤ) < specialAbsoluteGrade r → x r = 0 := by
  have hc : ∀ r : Fin 26, allowedSpecialLeadingRoot r → (-4 : ℤ) < specialAbsoluteGrade r → r = 7 ∨ r = 9 ∨ r = 24 ∨ r = 25 := by
    unfold allowedSpecialLeadingRoot
    decide
  intro r hr hg
  rcases hc r hr hg with rfl | rfl | rfl | rfl
  · exact h7
  · exact h9
  · exact h24
  · exact h25

private theorem allowedCoordinateBound_four {R : Type*} [Zero R]
    (x : Fin 26 → R) (h9 : x 9 = 0) (h24 : x 24 = 0) (h25 : x 25 = 0) :
    ∀ r, allowedSpecialLeadingRoot r → (4 : ℤ) < specialAbsoluteGrade r → x r = 0 := by
  have hc : ∀ r : Fin 26, allowedSpecialLeadingRoot r → (4 : ℤ) < specialAbsoluteGrade r → r = 9 ∨ r = 24 ∨ r = 25 := by
    unfold allowedSpecialLeadingRoot
    decide
  intro r hr hg
  rcases hc r hr hg with rfl | rfl | rfl
  · exact h9
  · exact h24
  · exact h25

private theorem allowedCoordinateBound_eight {R : Type*} [Zero R]
    (x : Fin 26 → R) (h9 : x 9 = 0) (h25 : x 25 = 0) :
    ∀ r, allowedSpecialLeadingRoot r → (8 : ℤ) < specialAbsoluteGrade r → x r = 0 := by
  have hc : ∀ r : Fin 26, allowedSpecialLeadingRoot r → (8 : ℤ) < specialAbsoluteGrade r → r = 9 ∨ r = 25 := by
    unfold allowedSpecialLeadingRoot
    decide
  intro r hr hg
  rcases hc r hr hg with rfl | rfl
  · exact h9
  · exact h25

private theorem allowedCoordinateBound_eleven {R : Type*} [Zero R]
    (x : Fin 26 → R) (h9 : x 9 = 0) :
    ∀ r, allowedSpecialLeadingRoot r → (11 : ℤ) < specialAbsoluteGrade r → x r = 0 := by
  have hc : ∀ r : Fin 26, allowedSpecialLeadingRoot r → (11 : ℤ) < specialAbsoluteGrade r → r = 9 := by
    unfold allowedSpecialLeadingRoot
    decide
  intro r hr hg
  have he := hc r hr hg
  subst r
  exact h9

private theorem leading4_of_raw {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) {u : TraceZero F}
    (hu : IsSpecialVector m u) (hn : u.val.2 0 2 ≠ 0)
    (h7 : u.val.2 0 5 = 0) (h9 : u.val.2 0 7 = 0) (h24 : u.val.2 2 6 = 0) (h25 : u.val.2 2 7 = 0) : SpecialLeadingAt 4 u := by
  refine ⟨hn,hu.support_bound_of_allowed hcard 4 ?_⟩
  exact allowedCoordinateBound_negFour (isotropyCoordinates u) h7 h9 h24 h25

private theorem leading7_of_raw {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) {u : TraceZero F}
    (hu : IsSpecialVector m u) (hn : u.val.2 0 5 ≠ 0)
    (h9 : u.val.2 0 7 = 0) (h24 : u.val.2 2 6 = 0) (h25 : u.val.2 2 7 = 0) : SpecialLeadingAt 7 u := by
  refine ⟨hn,hu.support_bound_of_allowed hcard 7 ?_⟩
  exact allowedCoordinateBound_four (isotropyCoordinates u) h9 h24 h25

private theorem leading24_of_raw {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) {u : TraceZero F}
    (hu : IsSpecialVector m u) (hn : u.val.2 2 6 ≠ 0)
    (h9 : u.val.2 0 7 = 0) (h25 : u.val.2 2 7 = 0) : SpecialLeadingAt 24 u := by
  refine ⟨hn,hu.support_bound_of_allowed hcard 24 ?_⟩
  exact allowedCoordinateBound_eight (isotropyCoordinates u) h9 h25

private theorem leading25_of_raw {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) {u : TraceZero F}
    (hu : IsSpecialVector m u) (hn : u.val.2 2 7 ≠ 0)
    (h9 : u.val.2 0 7 = 0) : SpecialLeadingAt 25 u := by
  refine ⟨hn,hu.support_bound_of_allowed hcard 25 ?_⟩
  exact allowedCoordinateBound_eleven (isotropyCoordinates u) h9

theorem elementary_reduction_leading7 {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    {u : TraceZero F} (hu : IsSpecialVector m u) (hl : SpecialLeadingAt 7 u) :
    ElementaryReducesToLowest hcard u := by
  obtain ⟨hs,h9,h25,h17,h16,h24,h15,h8,h23,h7,h21,h14,h0,h1,he,hn⟩ :=
    specialVector_A2_strict_descent hcard hu (hl.2 9 (by decide)) (hl.2 25 (by decide))
      (hl.2 17 (by decide)) (hl.2 16 (by decide)) (hl.2 24 (by decide))
      (hl.2 15 (by decide)) (hl.2 8 (by decide)) (hl.2 23 (by decide)) hl.1
  apply elementaryReducesToLowest_of_map hcard (fifthPivotDescent hcard u)
    (fifthPivotDescent_mem_elementary hcard u)
  apply elementary_reduction_leading4 hcard hs
  exact leading4_of_raw hcard hs hn h7 h9 h24 h25

theorem elementary_reduction_leading24 {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    {u : TraceZero F} (hu : IsSpecialVector m u) (hl : SpecialLeadingAt 24 u) :
    ElementaryReducesToLowest hcard u := by
  obtain ⟨hs,h9,h25,h17,h16,h24,h15,h8,he,hn⟩ :=
    specialVector_C3_strict_descent hcard hu (hl.2 9 (by decide)) (hl.2 25 (by decide))
      (hl.2 16 (by decide)) (hl.2 17 (by decide)) hl.1
  apply elementaryReducesToLowest_of_map hcard (thirdPivotDescent hcard u)
    (thirdPivotDescent_mem_elementary hcard u)
  apply elementary_reduction_leading7 hcard hs
  exact leading7_of_raw hcard hs hn h9 h24 h25

theorem elementary_reduction_leading25 {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    {u : TraceZero F} (hu : IsSpecialVector m u) (hl : SpecialLeadingAt 25 u) :
    ElementaryReducesToLowest hcard u := by
  obtain ⟨hs,h9,h25,h17,h16,he,hn⟩ := specialVector_C4_descent hcard hu (hl.2 9 (by decide)) hl.1
  apply elementaryReducesToLowest_of_map hcard (secondPivotDescent hcard u)
    (secondPivotDescent_mem_elementary hcard u)
  apply elementary_reduction_leading24 hcard hs
  exact leading24_of_raw hcard hs hn h9 h25

theorem elementary_reduction_leading9 {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    {u : TraceZero F} (hu : IsSpecialVector m u) (hl : SpecialLeadingAt 9 u) :
    ElementaryReducesToLowest hcard u := by
  let g := highestPivotModel hcard u
  have hs : IsSpecialVector m (g.val u) := hu.map_model g
  have h9 := highestPivot_top_eq_zero m u hl.1
  have hn := highestPivot_next_ne_zero m u hl.1
  apply elementaryReducesToLowest_of_map hcard g (highestPivotModel_mem_elementary hcard u)
  apply elementary_reduction_leading25 hcard hs
  exact leading25_of_raw hcard hs hn h9


end Atlas.ReeF4

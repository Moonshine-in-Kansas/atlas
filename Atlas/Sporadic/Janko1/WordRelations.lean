import Atlas.Sporadic.Janko1.CoordinateRepresentation

/-! Short local word identities. The displayed intermediate matrices are only
witnesses: every adjacent product is checked by ordinary kernel reduction. -/
namespace Atlas.Janko1

private def srTable : Fin 6 → Matrix (Fin 8) (Fin 8) Field :=
  ![!![1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 2, 1, 1, -3, 1, -3, -3;
      0, -1, 1, 3, -1, 3, -3, 2;
      0, -1, 3, 1, -3, 3, 2, -1;
      0, -3, 1, 3, -3, -2, -1, -1;
      0, -1, 3, 3, 2, 1, -1, -3;
      0, -3, 3, -2, -1, 1, -3, -1;
      0, -3, -2, 1, -1, 3, -1, -3],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, -5, 3, 3, -4, 3, -4, -4;
      0, -3, 4, -3, 3, -3, 0, 2;
      0, -3, -3, 4, 0, -3, 2, 3;
      0, -4, -3, 0, -5, -2, -1, -1;
      0, -3, -3, -3, 2, 4, 3, 0;
      0, -4, 0, -2, -1, -3, -5, -1;
      0, -4, -2, -3, -1, 0, -1, -5],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, -5, -3, -3, -4, -3, -4, -4;
      0, 3, 4, -3, -3, -3, 0, -2;
      0, 3, -3, 4, 0, -3, -2, -3;
      0, -4, 3, 0, -5, 2, -1, -1;
      0, 3, -3, -3, -2, 4, -3, 0;
      0, -4, 0, 2, -1, 3, -5, -1;
      0, -4, 2, 3, -1, 0, -1, -5],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 2, -1, -1, -3, -1, -3, -3;
      0, 1, 1, 3, 1, 3, 3, -2;
      0, 1, 3, 1, 3, 3, -2, 1;
      0, -3, -1, -3, -3, 2, -1, -1;
      0, 1, 3, 3, -2, 1, 1, 3;
      0, -3, -3, 2, -1, -1, -3, -1;
      0, -3, 2, -1, -1, -3, -1, -3],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxRecDepth 8192 in
private theorem sr_step : ∀ i : Fin 5,
    srTable i.castSucc * srTable 1 = srTable i.succ := by decide

private theorem sr_power : (srTable 1)^5 = 1 := by
  have h : ∀ i : Fin 6, (srTable 1)^i.val = srTable i := by
    intro i
    induction i using Fin.induction with
    | zero => decide
    | succ i hi =>
      simp only [Fin.val_castSucc] at hi
      rw [Fin.val_succ, pow_succ, hi]
      exact sr_step i
  have hn := h (Fin.last 5)
  have hl : srTable (Fin.last 5) = 1 := by decide
  exact hn.trans hl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
-- One short product of explicit eight-coordinate matrices.
private theorem sr_coordinates : coordinateRepresentation (S * R) = srTable 1 := by
  simp only [map_mul, coordinateRepresentation_P, coordinateRepresentation_Q,
    coordinateRepresentation_R, coordinateRepresentation_S]
  decide

theorem sr_pow : (S * R)^5 = 1 := by
  apply coordinateRepresentation_injective
  rw [map_pow, map_one, sr_coordinates]
  exact sr_power

private def pqsrTable : Fin 8 → Matrix (Fin 8) (Fin 8) Field :=
  ![!![1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, -3, 1, 3, -3, -2, -1, -1;
      0, 2, 1, 1, -3, 1, -3, -3;
      0, -1, 3, 3, 2, 1, -1, -3;
      0, -1, 1, 3, -1, 3, -3, 2;
      0, -3, 3, -2, -1, 1, -3, -1;
      0, -1, 3, 1, -3, 3, 2, -1;
      0, -3, -2, 1, -1, 3, -1, -3],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, -1, -3, 5, -1, 4, 0, 2;
      0, -4, 3, 4, -4, 5, -3, -3;
      0, 0, -3, -2, 3, 3, 3, -4;
      0, 2, 4, -3, 0, 3, 3, 3;
      0, -1, 0, 1, -5, 4, 2, 3;
      0, 3, -3, 0, 2, 3, -4, 3;
      0, -5, -2, 1, -1, 4, 3, 0],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, -3, -4, 0, -5, 0, 5, 5;
      0, 4, -3, -3, 0, 1, -4, 4;
      0, 4, -2, 4, 5, 4, 3, 5;
      0, -5, -2, 1, 5, -4, 5, 2;
      0, -5, -2, 4, -3, -4, 4, -5;
      0, 2, 4, 5, 4, -3, 2, 2;
      0, -4, 5, 0, 0, -3, -4, -1],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, -3, 4, 4, -5, -5, 2, -4;
      0, -4, -3, -2, -2, -2, 4, 5;
      0, 0, -3, 4, 1, 4, 5, 0;
      0, -5, 0, 5, 5, -3, 4, 0;
      0, 0, 1, 4, -4, -4, -3, -3;
      0, 5, -4, 3, 5, 4, 2, -4;
      0, 5, 4, 5, 2, -5, 2, -1],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, -1, -4, 0, 2, -1, 3, -5;
      0, -3, 3, -3, 4, 0, -3, -2;
      0, 5, 4, -2, -3, 1, 0, 1;
      0, -1, -4, 3, 0, -5, 2, -1;
      0, 4, 5, 3, 3, 4, 3, 4;
      0, 0, -3, 3, 3, 2, -4, 3;
      0, 2, -3, -4, 3, 3, 3, 0],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, -3, 2, -1, -1, -3, -1, -3;
      0, 1, 1, 3, 1, 3, 3, -2;
      0, 3, 1, 3, 3, -2, 1, 1;
      0, -3, -3, 2, -1, -1, -3, -1;
      0, -2, 1, 1, 3, 1, 3, 3;
      0, -1, -3, -1, -3, -3, 2, -1;
      0, -1, -3, -3, 2, -1, -1, -3],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxRecDepth 8192 in
private theorem pqsr_step : ∀ i : Fin 7,
    pqsrTable i.castSucc * pqsrTable 1 = pqsrTable i.succ := by decide

private theorem pqsr_power : (pqsrTable 1)^7 = 1 := by
  have h : ∀ i : Fin 8, (pqsrTable 1)^i.val = pqsrTable i := by
    intro i
    induction i using Fin.induction with
    | zero => decide
    | succ i hi =>
      simp only [Fin.val_castSucc] at hi
      rw [Fin.val_succ, pow_succ, hi]
      exact pqsr_step i
  have hn := h (Fin.last 7)
  have hl : pqsrTable (Fin.last 7) = 1 := by decide
  exact hn.trans hl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
-- One short product of explicit eight-coordinate matrices.
private theorem pqsr_coordinates : coordinateRepresentation (P * Q * S * R) = pqsrTable 1 := by
  simp only [map_mul, coordinateRepresentation_P, coordinateRepresentation_Q,
    coordinateRepresentation_R, coordinateRepresentation_S]
  decide

theorem pqsr_pow : (P * Q * S * R)^7 = 1 := by
  apply coordinateRepresentation_injective
  rw [map_pow, map_one, pqsr_coordinates]
  exact pqsr_power

private def rpTable : Fin 8 → Matrix (Fin 8) (Fin 8) Field :=
  ![!![1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, -1;
      0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, -1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, -1, 0, 0;
      0, 0, 0, 0, 0, 0, -1, 0],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, -1;
      0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, -1, 0, 0, 0, 0, 0;
      0, 0, 0, -1, 0, 0, 0, 0;
      0, 0, 0, 0, -1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, -1, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, -1;
      0, -1, 0, 0, 0, 0, 0, 0;
      0, 0, -1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, -1, 0, 0, 0;
      0, 0, 0, 0, 0, -1, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 1;
      0, -1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, -1, 0, 0, 0, 0],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, -1, 0, 0, 0;
      0, 0, 0, 0, 0, -1, 0, 0;
      0, 0, 0, 0, 0, 0, -1, 0;
      0, 0, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, -1, 0, 0, 0, 0, 0],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, -1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, -1, 0;
      0, 0, 0, 0, 0, 0, 0, -1;
      0, -1, 0, 0, 0, 0, 0, 0],
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxRecDepth 8192 in
private theorem rp_step : ∀ i : Fin 7,
    rpTable i.castSucc * rpTable 1 = rpTable i.succ := by decide

private theorem rp_power : (rpTable 1)^7 = 1 := by
  have h : ∀ i : Fin 8, (rpTable 1)^i.val = rpTable i := by
    intro i
    induction i using Fin.induction with
    | zero => decide
    | succ i hi =>
      simp only [Fin.val_castSucc] at hi
      rw [Fin.val_succ, pow_succ, hi]
      exact rp_step i
  have hn := h (Fin.last 7)
  have hl : rpTable (Fin.last 7) = 1 := by decide
  exact hn.trans hl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
-- One short product of explicit eight-coordinate matrices.
private theorem rp_coordinates : coordinateRepresentation (R * P) = rpTable 1 := by
  simp only [map_mul, coordinateRepresentation_P, coordinateRepresentation_Q,
    coordinateRepresentation_R, coordinateRepresentation_S]
  decide

theorem rp_pow : (R * P)^7 = 1 := by
  apply coordinateRepresentation_injective
  rw [map_pow, map_one, rp_coordinates]
  exact rp_power

end Atlas.Janko1

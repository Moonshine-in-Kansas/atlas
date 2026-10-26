import Mathlib.Algebra.Ring.Action.ConjAct
import Atlas.Algebra.CentralBracketExponential
import Atlas.Algebra.FiniteHadamardThree

/-! Source candidate: finite four-factor exponential identity for the
literal positive triple-edge Lie configuration. Nilpotence is explicit. -/

noncomputable section
namespace Atlas.Algebra

variable {S : Type*} [Ring S] [Algebra ℚ S]

/-- The increasing-height order is C,D/2,L/6,F/3. The last coefficient
is fixed by this order and by [C,D]=-F; it is not imported from a table. -/
theorem exp_tripleEdge_commutator
    (A B C D L F : S)
    (hA : IsNilpotent A) (hB : IsNilpotent B) (hC : IsNilpotent C)
    (hD : IsNilpotent D) (hL : IsNilpotent L) (hF : IsNilpotent F)
    (hCDsum : IsNilpotent (C + (1 / 2 : ℚ) • D))
    (hAB : A * B - B * A = C) (hAC : A * C - C * A = D)
    (hAD : A * D - D * A = L) (hAL : Commute A L)
    (hBC : Commute B C) (hBD : Commute B D)
    (hBL : B * L - L * B = F) (hCD : C * D - D * C = -F)
    (hCL : Commute C L) (hDL : Commute D L)
    (hBF : Commute B F) (hCF : Commute C F)
    (hDF : Commute D F) (hLF : Commute L F) :
    IsNilpotent.exp A * IsNilpotent.exp B * IsNilpotent.exp (-A) *
      IsNilpotent.exp (-B) =
        IsNilpotent.exp C * IsNilpotent.exp ((1 / 2 : ℚ) • D) *
          IsNilpotent.exp ((1 / 6 : ℚ) • L) *
            IsNilpotent.exp ((1 / 3 : ℚ) • F) := by
  let U := C + (1 / 2 : ℚ) • D
  let V := (1 / 6 : ℚ) • L
  let Q := U + V
  have hUV : Commute U V :=
    (hCL.add_left (hDL.smul_left (1 / 2 : ℚ))).smul_right (1 / 6 : ℚ)
  have hV : IsNilpotent V := hL.smul (1 / 6 : ℚ)
  have hQ : IsNilpotent Q := hUV.isNilpotent_add hCDsum hV
  have hQF : Commute Q F :=
    (hCF.add_left (hDF.smul_left (1 / 2 : ℚ))).add_left
      (hLF.smul_left (1 / 6 : ℚ))
  have hBQ : B * Q - Q * B = (1 / 6 : ℚ) • F := by
    calc
      B * Q - Q * B = (B * C - C * B) +
          (1 / 2 : ℚ) • (B * D - D * B) +
          (1 / 6 : ℚ) • (B * L - L * B) := by
        simp only [Q, U, V, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_sub]
        module
      _ = (1 / 6 : ℚ) • F := by
        rw [sub_eq_zero.mpr hBC.eq, sub_eq_zero.mpr hBD.eq, hBL]
        simp
  let u : Sˣ :=
    ⟨IsNilpotent.exp A, IsNilpotent.exp (-A),
      IsNilpotent.exp_mul_exp_neg_self hA, IsNilpotent.exp_neg_mul_exp_self hA⟩
  have hconj : IsNilpotent.exp A * B * IsNilpotent.exp (-A) = B + Q := by
    simpa only [Q, U, V, add_assoc] using
      exp_mul_mul_exp_neg_eq_add_add_half_add_sixth A B C D L hA hAB hAC hAD hAL
  have hBsum : IsNilpotent (B + Q) := by
    have h := hB.map
      (MulSemiringAction.toRingHom (ConjAct Sˣ) S (ConjAct.toConjAct u))
    change IsNilpotent (IsNilpotent.exp A * B * IsNilpotent.exp (-A)) at h
    rwa [hconj] at h
  have hfirst : IsNilpotent.exp (B + Q) * IsNilpotent.exp (-B) =
      IsNilpotent.exp Q * IsNilpotent.exp ((1 / 12 : ℚ) • F) := by
    have hsum : B + Q + -B = Q := by abel
    have hbr : (B + Q) * (-B) - (-B) * (B + Q) = (1 / 6 : ℚ) • F := by
      calc
        (B + Q) * (-B) - (-B) * (B + Q) = B * Q - Q * B := by noncomm_ring
        _ = _ := hBQ
    have h := exp_mul_eq_exp_add_mul_exp_half_bracket (B + Q) (-B)
      ((1 / 6 : ℚ) • F) hBsum hB.neg (hF.smul (1 / 6 : ℚ))
      (hsum.symm ▸ hQ) hbr
      ((hBF.add_left hQF).smul_right (1 / 6 : ℚ))
      (hBF.neg_left.smul_right (1 / 6 : ℚ))
    simpa only [hsum, smul_smul, show (1 / 2 : ℚ) * (1 / 6 : ℚ) = 1 / 12 by norm_num] using h
  have hsecond : IsNilpotent.exp U = IsNilpotent.exp C *
      IsNilpotent.exp ((1 / 2 : ℚ) • D) * IsNilpotent.exp ((1 / 4 : ℚ) • F) := by
    have hbr : C * ((1 / 2 : ℚ) • D) - ((1 / 2 : ℚ) • D) * C =
        (-1 / 2 : ℚ) • F := by
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, hCD]
      module
    have h := exp_mul_eq_exp_add_mul_exp_half_bracket C ((1 / 2 : ℚ) • D)
      ((-1 / 2 : ℚ) • F) hC (hD.smul (1 / 2 : ℚ))
      (hF.smul (-1 / 2 : ℚ)) hCDsum hbr
      (hCF.smul_right (-1 / 2 : ℚ))
      ((hDF.smul_left (1 / 2 : ℚ)).smul_right (-1 / 2 : ℚ))
    have hn : (1 / 2 : ℚ) • ((-1 / 2 : ℚ) • F) = -((1 / 4 : ℚ) • F) := by module
    rw [hn] at h
    change IsNilpotent.exp C * IsNilpotent.exp ((1 / 2 : ℚ) • D) =
      IsNilpotent.exp U * IsNilpotent.exp (-((1 / 4 : ℚ) • F)) at h
    have hm := congrArg (fun W => W * IsNilpotent.exp ((1 / 4 : ℚ) • F)) h
    simpa only [mul_assoc, IsNilpotent.exp_neg_mul_exp_self (hF.smul (1 / 4 : ℚ)),
      mul_one] using hm.symm
  have hFV : Commute (IsNilpotent.exp ((1 / 4 : ℚ) • F)) (IsNilpotent.exp V) := by
    have h : Commute ((1 / 4 : ℚ) • F) V :=
      (hLF.symm.smul_left (1 / 4 : ℚ)).smul_right (1 / 6 : ℚ)
    exact (commute_finiteExp_right (commute_finiteExp_right h).symm).symm
  have hFsum : IsNilpotent.exp ((1 / 4 : ℚ) • F) *
      IsNilpotent.exp ((1 / 12 : ℚ) • F) = IsNilpotent.exp ((1 / 3 : ℚ) • F) := by
    have hcomm : Commute ((1 / 4 : ℚ) • F) ((1 / 12 : ℚ) • F) :=
      ((Commute.refl F).smul_left (1 / 4 : ℚ)).smul_right (1 / 12 : ℚ)
    rw [← IsNilpotent.exp_add_of_commute hcomm (hF.smul _) (hF.smul _)]
    congr 1
    module
  have hmap := IsNilpotent.exp_smul (ConjAct.toConjAct u) hB
  change IsNilpotent.exp (IsNilpotent.exp A * B * IsNilpotent.exp (-A)) =
    IsNilpotent.exp A * IsNilpotent.exp B * IsNilpotent.exp (-A) at hmap
  rw [hconj] at hmap
  rw [← hmap, hfirst, IsNilpotent.exp_add_of_commute hUV hCDsum hV, hsecond]
  calc
    (IsNilpotent.exp C * IsNilpotent.exp ((1 / 2 : ℚ) • D) *
        IsNilpotent.exp ((1 / 4 : ℚ) • F) * IsNilpotent.exp V) *
        IsNilpotent.exp ((1 / 12 : ℚ) • F) =
      (IsNilpotent.exp C * IsNilpotent.exp ((1 / 2 : ℚ) • D) * IsNilpotent.exp V) *
        (IsNilpotent.exp ((1 / 4 : ℚ) • F) * IsNilpotent.exp ((1 / 12 : ℚ) • F)) := by
      rw [mul_assoc (IsNilpotent.exp C * IsNilpotent.exp ((1 / 2 : ℚ) • D))
        (IsNilpotent.exp ((1 / 4 : ℚ) • F)) (IsNilpotent.exp V), hFV.eq]
      simp only [mul_assoc]
    _ = _ := by rw [hFsum]

end Atlas.Algebra

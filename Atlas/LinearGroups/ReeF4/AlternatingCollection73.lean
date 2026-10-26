import Atlas.LinearGroups.ReeF4.AlternatingFactorSimp
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem alternatingCollection_73_formula {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u1 u3 : F) (w : Carrier F) :
    alternatingLongFormula m 3 u3 (alternatingLongFormula m 1 u1 w) =
    alternatingLongFormula m 1 (u1) (alternatingLongFormula m 3 (u3) (w)) := by
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp only [Fin.reduceFinMk, ree_f4_factor_rows, _root_.map_add, _root_.map_mul, _root_.map_pow, _root_.map_zero, _root_.map_one, SuzukiFamily.theta_square hcard] <;> ring_nf <;> simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.reduceFinMk, ree_f4_factor_rows, _root_.map_add, _root_.map_mul, _root_.map_pow, _root_.map_zero, _root_.map_one, SuzukiFamily.theta_square hcard] <;> ring_nf <;> simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]
end Atlas.ReeF4

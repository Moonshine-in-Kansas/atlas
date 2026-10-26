import Atlas.LinearGroups.ReeF4.AlternatingFactorSimp
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem alternatingCollection_60_formula {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a0 b0 a3 b3 : F) (w : Carrier F) :
    alternatingShortFormula m 3 a3 b3 (alternatingShortFormula m 0 a0 b0 w) =
    alternatingShortFormula m 0 (a0) (b0) (alternatingLongFormula m 0 (a3*b0) (alternatingShortFormula m 1 (a3*(theta F m a0)) (b3*(theta F m b0)+a0*a0*b3*(theta F m a0)+a0*b0*b3+a3*(theta F m a3)*(theta F m b0)) (alternatingLongFormula m 1 (b0*b3+a0*b3*(theta F m a0)) (alternatingShortFormula m 2 (a0*(theta F m a3)) (b0*(theta F m b3)+a3*a3*b0*(theta F m a3)+a3*b0*b3+a0*a3*a3*(theta F m a0)*(theta F m a3)+a0*a3*b3*(theta F m a0)) (alternatingLongFormula m 2 (a0*a3*(theta F m a3)+a0*b3) (alternatingShortFormula m 3 (a3) (b3) (w))))))) := by
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp only [Fin.reduceFinMk, ree_f4_factor_rows, _root_.map_add, _root_.map_mul, _root_.map_pow, _root_.map_zero, _root_.map_one, SuzukiFamily.theta_square hcard] <;> ring_nf <;> simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.reduceFinMk, ree_f4_factor_rows, _root_.map_add, _root_.map_mul, _root_.map_pow, _root_.map_zero, _root_.map_one, SuzukiFamily.theta_square hcard] <;> ring_nf <;> simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]
end Atlas.ReeF4

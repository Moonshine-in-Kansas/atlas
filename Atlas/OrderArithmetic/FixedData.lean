import Atlas.OrderArithmetic.Parameters
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.FinCases

namespace Atlas.OrderArithmetic

/-- Literal prime-factor products from Appendix A. -/
def fixedOrder : FixedLabel → ℕ
  | .M11 => 2^4 * 3^2 * 5 * 11
  | .M12 => 2^6 * 3^3 * 5 * 11
  | .M22 => 2^7 * 3^2 * 5 * 7 * 11
  | .M23 => 2^7 * 3^2 * 5 * 7 * 11 * 23
  | .M24 => 2^10 * 3^3 * 5 * 7 * 11 * 23
  | .J1 => 2^3 * 3 * 5 * 7 * 11 * 19
  | .J2 => 2^7 * 3^3 * 5^2 * 7
  | .J3 => 2^7 * 3^5 * 5 * 17 * 19
  | .J4 => 2^21 * 3^3 * 5 * 7 * 11^3 * 23 * 29 * 31 * 37 * 43
  | .HS => 2^9 * 3^2 * 5^3 * 7 * 11
  | .McL => 2^7 * 3^6 * 5^3 * 7 * 11
  | .He => 2^10 * 3^3 * 5^2 * 7^3 * 17
  | .Ru => 2^14 * 3^3 * 5^3 * 7 * 13 * 29
  | .Suz => 2^13 * 3^7 * 5^2 * 7 * 11 * 13
  | .ON => 2^9 * 3^4 * 5 * 7^3 * 11 * 19 * 31
  | .Co3 => 2^10 * 3^7 * 5^3 * 7 * 11 * 23
  | .Co2 => 2^18 * 3^6 * 5^3 * 7 * 11 * 23
  | .Fi22 => 2^17 * 3^9 * 5^2 * 7 * 11 * 13
  | .HN => 2^14 * 3^6 * 5^6 * 7 * 11 * 19
  | .Ly => 2^8 * 3^7 * 5^6 * 7 * 11 * 31 * 37 * 67
  | .Th => 2^15 * 3^10 * 5^3 * 7^2 * 13 * 19 * 31
  | .Fi23 => 2^18 * 3^13 * 5^2 * 7 * 11 * 13 * 17 * 23
  | .Co1 => 2^21 * 3^9 * 5^4 * 7^2 * 11 * 13 * 23
  | .Fi24prime => 2^21 * 3^16 * 5^2 * 7^3 * 11 * 13 * 17 * 23 * 29
  | .Baby => 2^41 * 3^13 * 5^6 * 7^2 * 11 * 13 * 17 * 19 * 23 * 31 * 47
  | .Monster => 2^46 * 3^20 * 5^9 * 7^6 * 11^2 * 13^3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71
  | .Tits => 2^11 * 3^3 * 5^2 * 13

/-- Decimal transcription, checked against the factor products below. -/
def fixedDecimal : FixedLabel → ℕ
  | .M11 => 7920
  | .M12 => 95040
  | .M22 => 443520
  | .M23 => 10200960
  | .M24 => 244823040
  | .J1 => 175560
  | .J2 => 604800
  | .J3 => 50232960
  | .J4 => 86775571046077562880
  | .HS => 44352000
  | .McL => 898128000
  | .He => 4030387200
  | .Ru => 145926144000
  | .Suz => 448345497600
  | .ON => 460815505920
  | .Co3 => 495766656000
  | .Co2 => 42305421312000
  | .Fi22 => 64561751654400
  | .HN => 273030912000000
  | .Ly => 51765179004000000
  | .Th => 90745943887872000
  | .Fi23 => 4089470473293004800
  | .Co1 => 4157776806543360000
  | .Fi24prime => 1255205709190661721292800
  | .Baby => 4154781481226426191177580544000000
  | .Monster => 808017424794512875886459904961710757005754368000000000
  | .Tits => 17971200

theorem fixedOrder_eq_decimal (s : FixedLabel) : fixedOrder s = fixedDecimal s := by
  cases s <;> norm_num [fixedOrder, fixedDecimal]

theorem fixedOrder_injective : Function.Injective fixedOrder := by
  intro x y h
  cases x <;> cases y <;> simp_all [fixedOrder_eq_decimal, fixedDecimal]

theorem fixedOrder_pos (s : FixedLabel) : 0 < fixedOrder s := by
  cases s <;> norm_num [fixedOrder]

theorem fixedOrder_not_prime (s : FixedLabel) : ¬ (fixedOrder s).Prime := by
  cases s <;> norm_num [fixedOrder]

/-- Every base used in the literal products is prime. -/
theorem fixedOrder_factor_bases_prime :
    ∀ p ∈ ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 59, 67, 71] : List ℕ),
      Nat.Prime p := by
  norm_num

end Atlas.OrderArithmetic

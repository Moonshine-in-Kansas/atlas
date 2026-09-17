import Atlas.Codes.TernaryConstantHexads

namespace Atlas.Codes

/-- A constant-support word can be shifted by a constant and remain of weight
below twelve only by staying itself or becoming the negative complement. -/
theorem ternaryConstant_shift_short (s : Finset (Fin 12)) (w : TernaryWord)
    (hw : ternaryWeight w < 12) (a : ZMod 3)
    (ha : ∀ i, ternaryTriadWord s i-w i=a) :
    w=ternaryTriadWord s ∨ w= -ternaryTriadWord sᶜ := by
  have he (i : Fin 12) : w i=ternaryTriadWord s i-a := by
    linear_combination -(ha i)
  have hcases : ∀ b : ZMod 3, b=0 ∨ b=1 ∨ b=2 := by decide +kernel
  rcases hcases a with rfl|rfl|rfl
  · left
    funext i
    simpa using he i
  · right
    funext i
    rw [he]
    by_cases hi : i ∈ s <;> simp [ternaryTriadWord,hi] <;> decide
  · have hn (i : Fin 12) : w i ≠ 0 := by
      rw [he]
      by_cases hi : i ∈ s <;> norm_num [ternaryTriadWord,hi] <;> decide
    have hc : ternaryWeight w=12 := by simp [ternaryWeight,hn]
    omega

end Atlas.Codes

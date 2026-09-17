import Atlas.Fischer.CountingColumnRule

namespace Atlas.Fischer

theorem countingColumnDelta_bound (n d : ℕ) (h : countingColumnDelta n=some d) : d ≤ 1 := by
  unfold countingColumnDelta at h
  split_ifs at h <;> simp_all <;> omega

theorem countingSigned_power_values (s e : ℕ) (he : e ≤ 2) :
    ∃ i : Fin 6, (-1 : ℤ)^s * (-3 : ℤ)^e=countingSignedWeight i := by
  rcases neg_one_pow_eq_or ℤ s with hs | hs <;>
    interval_cases e <;> rw [hs] <;> norm_num [countingSignedWeight] <;> decide

/-- Every nonzero optional column contribution belongs to the six displayed
signed weights. This is derived from the binary tests and exponent bound. -/
theorem countingColumnWeight_values (epsilon : ℕ) (D E F : Finset (Fin 6))
    (g b h : CountingColumnVector) (w : ℤ)
    (hw : countingColumnWeight epsilon D E F g b h=some w) :
    ∃ i : Fin 6, w=countingSignedWeight i := by
  simp only [countingColumnWeight, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hw
  rcases hw with ⟨d0,h0,d1,h1,d2,h2,d3,h3,rfl⟩
  apply countingSigned_power_values
  have hd0 := countingColumnDelta_bound _ _ h0
  have hd1 := countingColumnDelta_bound _ _ h1
  have hd2 := countingColumnDelta_bound _ _ h2
  have hd3 := countingColumnDelta_bound _ _ h3
  have hd4 : (epsilon+d0+d1+d2+d3)%2 ≤ 1 := by omega
  omega

theorem countingWeightHistogram_moment (w : Option ℤ)
    (hw : w=none ∨ ∃ i : Fin 6, w=some (countingSignedWeight i)) :
    countingHistogramMoment (countingWeightHistogram w)=w.getD 0 := by
  rcases hw with rfl | ⟨i,rfl⟩
  · simp [countingHistogramMoment,countingWeightHistogram]
  · fin_cases i <;> decide

theorem countingColumnWeight_moment (epsilon : ℕ) (D E F : Finset (Fin 6))
    (g b h : CountingColumnVector) :
    countingHistogramMoment (countingWeightHistogram (countingColumnWeight epsilon D E F g b h)) =
      (countingColumnWeight epsilon D E F g b h).getD 0 := by
  apply countingWeightHistogram_moment
  cases he : countingColumnWeight epsilon D E F g b h with
  | none => exact Or.inl rfl
  | some w =>
    obtain ⟨i,hi⟩ := countingColumnWeight_values epsilon D E F g b h w he
    exact Or.inr ⟨i,congrArg some hi⟩

theorem countingHistogramMoment_sum {ι : Type*} [Fintype ι]
    (f : ι → CountingSignedHistogram) :
    countingHistogramMoment (fun k => ∑ i, f i k) =
      ∑ i, countingHistogramMoment (f i) := by
  simp only [countingHistogramMoment, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

end Atlas.Fischer

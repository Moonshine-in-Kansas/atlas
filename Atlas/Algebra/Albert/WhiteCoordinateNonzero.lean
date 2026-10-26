import Atlas.Algebra.Albert.RankOne

namespace Atlas.Albert
variable {F : Type*} [Field F]

theorem whiteZero_exists_offDiagonal (x : Carrier F) (hx : x≠0)
    (ha : adjoint x=0) (ht : trace x=0) : ∃ i j, x.2 i j≠0 := by
  by_contra h
  push_neg at h
  have ho : x.2=0 := by ext i j; exact h i j
  have hab : x.1 0*x.1 1=0 := by
    have := congrArg (fun y : Carrier F=>y.1 2) ha
    simpa [adjoint,ho,SplitOctonion.norm] using this
  have hac : x.1 2*x.1 0=0 := by
    have := congrArg (fun y : Carrier F=>y.1 1) ha
    simpa [adjoint,ho,SplitOctonion.norm] using this
  have hbc : x.1 1*x.1 2=0 := by
    have := congrArg (fun y : Carrier F=>y.1 0) ha
    simpa [adjoint,ho,SplitOctonion.norm] using this
  change x.1 0+x.1 1+x.1 2=0 at ht
  have h0 : x.1 0=0 := by
    by_contra hn
    have hb := (mul_eq_zero.mp hab).resolve_left hn
    have hc := (mul_eq_zero.mp hac).resolve_right hn
    apply hn
    simpa [hb,hc] using ht
  have h1 : x.1 1=0 := by
    by_contra hn
    have hc := (mul_eq_zero.mp hbc).resolve_left hn
    apply hn
    simpa [h0,hc] using ht
  have h2 : x.1 2=0 := by simpa [h0,h1] using ht
  apply hx
  apply Prod.ext
  · ext i; fin_cases i <;> assumption
  · exact ho

end Atlas.Albert

import Atlas.LinearGroups.F4.NearPointGeometry

/-! The coordinate complement of the intrinsic near nine-space on the white cone. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def nonNearCoordinates (x : Carrier F) : Fin 15 → F :=
  ![x.2 0 4,x.2 0 5,x.2 0 6,x.2 0 7,
    x.2 1 3,x.2 1 5,x.2 1 6,x.2 1 7,
    x.2 2 1,x.2 2 2,x.2 2 3,x.2 2 4,x.2 2 5,x.2 2 6,x.2 2 7]

/-- On the trace-zero rank-one cone, vanishing of the fifteen transverse
coordinates forces membership in the actual cross-image nine-space. -/
theorem mem_near_of_nonNearCoordinates_zero (x : Carrier F)
    (ha : adjoint x = 0) (ht : trace x = 0) (hz : nonNearCoordinates x = 0) :
    x ∈ parabolicImageZero (F:=F) := by
  have h (i : Fin 15) : nonNearCoordinates x i = 0 := congrFun hz i
  have h0 : x.2 0 4 = 0 := h 0
  have h1 : x.2 0 5 = 0 := h 1
  have h2 : x.2 0 6 = 0 := h 2
  have h3 : x.2 0 7 = 0 := h 3
  have h4 : x.2 1 3 = 0 := h 4
  have h5 : x.2 1 5 = 0 := h 5
  have h6 : x.2 1 6 = 0 := h 6
  have h7 : x.2 1 7 = 0 := h 7
  have h8 : x.2 2 1 = 0 := h 8
  have h9 : x.2 2 2 = 0 := h 9
  have h10 : x.2 2 3 = 0 := h 10
  have h11 : x.2 2 4 = 0 := h 11
  have h12 : x.2 2 5 = 0 := h 12
  have h13 : x.2 2 6 = 0 := h 13
  have h14 : x.2 2 7 = 0 := h 14
  have hn0 : SplitOctonion.norm (x.2 0) = 0 := by simp [SplitOctonion.norm,h0,h1,h2,h3]
  have hn1 : SplitOctonion.norm (x.2 1) = 0 := by simp [SplitOctonion.norm,h4,h5,h6,h7]
  have hn2 : SplitOctonion.norm (x.2 2) = 0 := by simp [SplitOctonion.norm,h8,h9,h10,h11,h12,h13,h14]
  have hab : x.1 0 * x.1 1 = 0 := by
    have he := congrArg (fun y : Carrier F => y.1 2) ha
    simpa [adjoint,hn2] using he
  have hbc : x.1 1 * x.1 2 = 0 := by
    have he := congrArg (fun y : Carrier F => y.1 0) ha
    simpa [adjoint,hn0] using he
  have hca : x.1 2 * x.1 0 = 0 := by
    have he := congrArg (fun y : Carrier F => y.1 1) ha
    simpa [adjoint,hn1] using he
  change x.1 0 + x.1 1 + x.1 2 = 0 at ht
  have ha0 : x.1 0 = 0 := by
    have hs : x.1 0 ^ 2 = 0 := by linear_combination x.1 0 * ht - hab - hca
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hs
  have hb0 : x.1 1 = 0 := by
    have hs : x.1 1 ^ 2 = 0 := by linear_combination x.1 1 * ht - hab - hbc
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hs
  have hc0 : x.1 2 = 0 := by simpa [ha0,hb0] using ht
  have he : nearVector (x.2 2 0) (nearSpinCoordinates x) = x := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [nearVector,upperSpinEmbed,parabolicVector,ha0,hb0,hc0]
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [nearVector,nearSpinCoordinates,upperSpinEmbed,parabolicVector,
          h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14]
  rw [←he]
  exact nearVector_mem_imageZero _ _

end Atlas.F4

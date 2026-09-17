import Atlas.Fischer.CountingHexacodeProjection
import Atlas.Fischer.CountingHexacodeTrace

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra
attribute [local instance] Classical.propDecidable

/-- A nonzero word spans its actual four-element double-zero fiber. -/
def countingHexDoubleZeroScalarEquiv (i j : Fin 6) (hij : i ≠ j)
    (h : countingHexDoubleZero i j) (hh : h ≠ 0) :
    CountingFour ≃ countingHexDoubleZero i j :=
  Equiv.ofBijective (fun a : CountingFour => a • h) (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨smul_left_injective CountingFour hh,?_⟩
    rw [goldenFour_card,← Nat.card_eq_fintype_card,countingHexDoubleZero_card i j hij])

/-- The three nonzero words on a four-set are precisely the nonzero scalar multiples. -/
def countingHexDoubleZeroNonzeroEquiv (i j : Fin 6) (hij : i ≠ j)
    (h : countingHexDoubleZero i j) (hh : h ≠ 0) :
    {a : CountingFour // a ≠ 0} ≃ {w : countingHexDoubleZero i j // w ≠ 0} :=
  Equiv.subtypeEquiv (countingHexDoubleZeroScalarEquiv i j hij h hh) (by
    intro a
    change a ≠ 0 ↔ a • h ≠ 0
    simp [hh])

/-- Two equal nonzero-coordinate ratios and a common zero force proportionality.
This is the distance-four argument needed for the intersection-three row. -/
theorem countingHex_equal_ratios (g h : countingHexacode) (i j k : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hgi : g.val i ≠ 0) (hgj : g.val j ≠ 0)
    (hgk : g.val k=0) (hhk : h.val k=0)
    (hr : h.val i/g.val i=h.val j/g.val j) :
    h=(h.val i/g.val i) • g := by
  let e : Fin 3 ↪ Fin 6 := ⟨![i,j,k],by
    intro x y he
    fin_cases x <;> fin_cases y <;> simp_all⟩
  have hz : h-(h.val i/g.val i) • g=0 := by
    apply countingHex_three_zeros _ e
    intro x
    fin_cases x
    · change h.val i-(h.val i/g.val i)*g.val i=0
      rw [div_mul_cancel₀ _ hgi,sub_self]
    · change h.val j-(h.val i/g.val i)*g.val j=0
      rw [hr,div_mul_cancel₀ _ hgj,sub_self]
    · change h.val k-(h.val i/g.val i)*g.val k=0
      simp [hgk,hhk]
  exact sub_eq_zero.mp hz

/-- The sum of the six ratios is zero, including the convention division by zero=0. -/
theorem countingHex_ratio_sum (h g : countingHexacode) :
    (∑ i : Fin 6, h.val i/g.val i)=0 := by
  simp_rw [countingFour_div]
  exact countingHexacode_hermitian_orthogonal h g

end Atlas.Fischer

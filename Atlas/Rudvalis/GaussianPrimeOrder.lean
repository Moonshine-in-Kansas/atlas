import Atlas.Conway.RationalPrimeOrder
import Atlas.Rudvalis.GaussianLatticeFinite
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! The existing general rational cyclotomic obstruction, applied to the actual
56-dimensional lattice group. No Conway-group construction is used. The weaker
rational bound already excludes the two primes required for local fusion. -/
namespace Atlas.Rudvalis

noncomputable def gaussianRationalMatrix : gaussianLatticeGroup →* Matrix Coordinate Coordinate ℚ :=
  LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp gaussianLatticeGroup.subtype)

theorem gaussianRationalMatrix_injective : Function.Injective gaussianRationalMatrix :=
  LinearMap.toMatrixAlgEquiv'.injective.comp
    (LinearEquiv.toLinearMap_injective.comp Subtype.val_injective)

theorem gaussian_prime_order_bound (g : gaussianLatticeGroup) (p : ℕ) (hp : p.Prime)
    (hg : orderOf g=p) : p-1≤56 := by
  have hpow : gaussianRationalMatrix g^p=1 := by
    rw [←map_pow,←hg,pow_orderOf_eq_one,map_one]
  have hne : gaussianRationalMatrix g≠1 := by
    intro he
    have hgone := gaussianRationalMatrix_injective (he.trans gaussianRationalMatrix.map_one.symm)
    rw [hgone,orderOf_one] at hg
    exact hp.ne_one hg.symm
  simpa using Atlas.Conway.matrix_prime_order_dimension (gaussianRationalMatrix g) p hp hpow hne

theorem gaussian_no_order_73 (g : gaussianLatticeGroup) : orderOf g≠73 := by
  intro h
  have hb := gaussian_prime_order_bound g 73 (by norm_num) h
  omega

theorem gaussian_no_order_521 (g : gaussianLatticeGroup) : orderOf g≠521 := by
  intro h
  have hb := gaussian_prime_order_bound g 521 (by norm_num) h
  omega

theorem gaussian_subgroup_prime_divisor_bound (K : Subgroup gaussianLatticeGroup)
    (p : ℕ) (hp : p.Prime) (hdiv : p∣Nat.card K) : p-1≤56 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' p hdiv
  apply gaussian_prime_order_bound g.val p hp
  rw [orderOf_submonoid]
  exact hg

theorem gaussian_subgroup_not_dvd_73 (K : Subgroup gaussianLatticeGroup) : ¬73∣Nat.card K := by
  intro h
  have hb := gaussian_subgroup_prime_divisor_bound K 73 (by norm_num) h
  omega

theorem gaussian_subgroup_not_dvd_521 (K : Subgroup gaussianLatticeGroup) : ¬521∣Nat.card K := by
  intro h
  have hb := gaussian_subgroup_prime_divisor_bound K 521 (by norm_num) h
  omega

/-- The arithmetic part of local fusion; the remaining size27 must be excluded
by the already identified full coordinate-frame stabilizer. -/
theorem gaussian_fusion_size_alternatives (K : Subgroup gaussianLatticeGroup) (n : ℕ)
    (hn : n=27 ∨ n=219 ∨ n=1563 ∨ n=1755) (hd : n∣Nat.card K) : n=27 ∨ n=1755 := by
  rcases hn with rfl|rfl|rfl|rfl
  · exact Or.inl rfl
  · exact (gaussian_subgroup_not_dvd_73 K ((by norm_num : 73∣219).trans hd)).elim
  · exact (gaussian_subgroup_not_dvd_521 K ((by norm_num : 521∣1563).trans hd)).elim
  · exact Or.inr rfl

end Atlas.Rudvalis


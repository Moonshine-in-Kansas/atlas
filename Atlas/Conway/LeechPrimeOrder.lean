import Atlas.Conway.RationalPrimeOrder
import Atlas.Lattices.LeechFullIsometries

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

def leechRationalMatrix : LeechIsometryGroup →* Matrix Omega Omega ℚ :=
  LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (rationalLatticeIsometries.subtype.comp fullIsometryExtension))

theorem leechRationalMatrix_injective : Function.Injective leechRationalMatrix :=
  LinearMap.toMatrixAlgEquiv'.injective.comp
    (LinearEquiv.toLinearMap_injective.comp
      (Subtype.val_injective.comp fullIsometryExtension_bijective.1))

theorem leech_prime_order_le (g : LeechIsometryGroup) (p : ℕ) (hp : p.Prime)
    (hg : orderOf g = p) : p ≤ 23 := by
  have hpow : leechRationalMatrix g ^ p = 1 := by
    rw [← map_pow,← hg,pow_orderOf_eq_one,map_one]
  have hne : leechRationalMatrix g ≠ 1 := by
    intro he
    have hgone := leechRationalMatrix_injective (he.trans leechRationalMatrix.map_one.symm)
    rw [hgone,orderOf_one] at hg
    exact hp.ne_one hg.symm
  have hb := matrix_prime_order_dimension (leechRationalMatrix g) p hp hpow hne
  have hc : Fintype.card Omega = 24 := by decide
  rw [hc] at hb
  by_contra hn
  have he : p = 24 ∨ p = 25 := by omega
  rcases he with rfl | rfl <;> norm_num at hp

end Atlas.Conway

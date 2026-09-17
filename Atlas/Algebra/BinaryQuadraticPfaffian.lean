import Atlas.Algebra.BinaryQuadraticPolarCoefficients
import Atlas.Algebra.BinaryWalshRank

noncomputable section
namespace Atlas.Algebra
open Atlas.Codes

/-- Complementary-coefficient columns of the four-dimensional alternating form. -/
def binaryPfaffianColumn (c : Fin 11 → Bit) : Fin 4 → BinaryFour :=
  ![![0,c 10,c 9,c 8],![c 10,0,c 7,c 6],![c 9,c 7,0,c 5],![c 8,c 6,c 5,0]]

set_option maxHeartbeats 1000000 in
theorem binaryAlternatingFour_pfaffian_column (c : Fin 11 → Bit) (j : Fin 4) (t : BinaryFour) :
    binaryAlternatingFour c (binaryPfaffianColumn c j) t=binaryQuadraticPfaffian c*t j := by
  fin_cases j <;> simp [binaryAlternatingFour,binaryPfaffianColumn,binaryQuadraticPfaffian] <;>
    ring_nf <;> simp only [show (2 : Bit)=0 from rfl,mul_zero,zero_add,add_zero]

/-- Full polar rank means injectivity of the actual four-variable polar map. -/
theorem binaryFourPolar_injective (q : QuadraticMap Bit BinaryFour Bit)
    (hr : binaryWalshPolarRank q=4) : Function.Injective q.polarBilin := by
  have hd := q.polarBilin.finrank_range_add_finrank_ker
  have hdim : Module.finrank Bit BinaryFour=4 := by simp [BinaryFour]
  change binaryWalshPolarRank q + Module.finrank Bit q.polarBilin.ker=
    Module.finrank Bit BinaryFour at hd
  rw [hr,hdim] at hd
  have hk : q.polarBilin.ker=⊥ := Submodule.finrank_eq_zero.mp (by omega)
  exact LinearMap.ker_eq_bot.mp hk

/-- Full polar rank forces the actual Pfaffian to be one over F₂. -/
theorem binaryQuadraticPfaffian_eq_one (c : Fin 11 → Bit)
    (hr : binaryWalshPolarRank (binaryNormalizedQuadratic c)=4) : binaryQuadraticPfaffian c=1 := by
  have hb : ∀ b : Bit, b=0 ∨ b=1 := by decide
  rcases hb (binaryQuadraticPfaffian c) with hp | hp
  · have hinj := binaryFourPolar_injective (binaryNormalizedQuadratic c) hr
    have hv (j : Fin 4) : binaryPfaffianColumn c j=0 := by
      apply hinj
      apply LinearMap.ext
      intro t
      rw [binaryNormalizedQuadratic_polar,binaryAlternatingFour_pfaffian_column,hp,zero_mul,map_zero]
      rfl
    have h0 := congrArg (fun v : BinaryFour => v 1) (hv 0)
    have h1 := congrArg (fun v : BinaryFour => v 2) (hv 0)
    have h2 := congrArg (fun v : BinaryFour => v 3) (hv 0)
    have h3 := congrArg (fun v : BinaryFour => v 2) (hv 1)
    have h4 := congrArg (fun v : BinaryFour => v 3) (hv 1)
    have h5 := congrArg (fun v : BinaryFour => v 3) (hv 2)
    simp [binaryPfaffianColumn] at h0 h1 h2 h3 h4 h5
    have he : (![1,0,0,0] : BinaryFour)=0 := by
      apply hinj
      apply LinearMap.ext
      intro t
      rw [binaryNormalizedQuadratic_polar]
      simp [binaryAlternatingFour,h0,h1,h2,h3,h4,h5]
    have hf := congrArg (fun v : BinaryFour => v 0) he
    norm_num at hf
  · exact hp

end Atlas.Algebra

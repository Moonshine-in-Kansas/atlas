import Atlas.Fischer.ParkerLoopLifts
import Atlas.Algebra.BinaryCocycleSplitting

namespace Atlas.Fischer
open Atlas.Codes

/-- The sign coordinate of a loop permutation on the zero-sign representatives. -/
def parkerPermutationCorrection (e : Equiv.Perm ParkerLoop) (a : golay) : Bit := (e (a,0)).2

theorem parkerPermutationCorrection_zero (e : Equiv.Perm ParkerLoop)
    (hfix : ∀ s, e (0,s)=(0,s)) : parkerPermutationCorrection e 0=0 :=
  congrArg Prod.snd (hfix 0)

/-- A multiplicative loop permutation fixing the central signs is determined
by its induced code map and its correcting function on zero-sign representatives. -/
theorem parkerPermutation_normal_form (e : Equiv.Perm ParkerLoop)
    (g : golay ≃ₗ[Bit] golay)
    (hmul : ∀ x y, e (parkerLoopMultiply x y)=parkerLoopMultiply (e x) (e y))
    (hfix : ∀ s, e (0,s)=(0,s)) (hcode : ∀ x, (e x).1=g x.1)
    (x : ParkerLoop) : e x=(g x.1,x.2+parkerPermutationCorrection e x.1) := by
  have hx : parkerLoopMultiply (0,x.2) (x.1,0)=x := by
    apply Prod.ext <;> simp [parkerLoopMultiply,parkerMultiply]
  rw [← hx,hmul,hfix]
  apply Prod.ext
  · change 0+(e (x.1,0)).1=g (parkerLoopMultiply (0,x.2) (x.1,0)).1
    rw [hcode]
    simp [parkerLoopMultiply,parkerMultiply]
  · change x.2+(e (x.1,0)).2+parkerGolayFactorSet 0 (e (x.1,0)).1 =
      (parkerLoopMultiply (0,x.2) (x.1,0)).2+
        parkerPermutationCorrection e (parkerLoopMultiply (0,x.2) (x.1,0)).1
    rw [hx]
    simp [parkerPermutationCorrection]

/-- The sign function of every actual standard loop automorphism satisfies
the exact factor-set correction equation. -/
theorem parkerPermutationCorrection_equation (e : Equiv.Perm ParkerLoop)
    (g : golay ≃ₗ[Bit] golay)
    (hmul : ∀ x y, e (parkerLoopMultiply x y)=parkerLoopMultiply (e x) (e y))
    (hfix : ∀ s, e (0,s)=(0,s)) (hcode : ∀ x, (e x).1=g x.1) (a b : golay) :
    parkerPermutationCorrection e (a+b)+parkerPermutationCorrection e a+
      parkerPermutationCorrection e b=
        parkerGolayFactorSet (g a) (g b)+parkerGolayFactorSet a b := by
  have h := hmul (a,0) (b,0)
  rw [parkerPermutation_normal_form e g hmul hfix hcode,
    parkerPermutation_normal_form e g hmul hfix hcode,
    parkerPermutation_normal_form e g hmul hfix hcode] at h
  have he := congrArg Prod.snd h
  change (0+0+parkerGolayFactorSet a b)+parkerPermutationCorrection e (a+b)=
    (0+parkerPermutationCorrection e a)+(0+parkerPermutationCorrection e b)+
      parkerGolayFactorSet (g a) (g b) at he
  simp only [zero_add] at he
  have hh := congrArg (fun z => z+parkerGolayFactorSet a b+
    parkerPermutationCorrection e a+parkerPermutationCorrection e b) he
  convert hh using 1 <;> ring_nf <;>
    simp only [show (2 : Bit)=0 from rfl,mul_zero,zero_add,add_zero]

end Atlas.Fischer

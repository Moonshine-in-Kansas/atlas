import Atlas.Algebra.IcosianModuloTwoKernel
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
namespace Atlas.Algebra

/-- The two-sided ideal whose elements are exactly twice icosians. -/
def icosianTwiceIdeal : Ideal icosianOrder := RingHom.ker icosianModuloTwo

instance icosianTwiceIdeal_twoSided : icosianTwiceIdeal.IsTwoSided := inferInstanceAs
  (RingHom.ker icosianModuloTwo).IsTwoSided

theorem icosianTwiceIdeal_mem (x : icosianOrder) :
    x ∈ icosianTwiceIdeal ↔ ∃ y : icosianOrder,x=2*y :=
  icosianModuloTwo_eq_zero_iff_two_mul x

/-- The actual scalar ring quotient by twice the order is the full two-by-two matrix ring. -/
def icosianModuloTwoQuotient : icosianOrder ⧸ icosianTwiceIdeal ≃+* IcosianMatrix :=
  RingHom.quotientKerEquivOfSurjective icosianModuloTwo_surjective

theorem icosianModuloTwoQuotient_mk (x : icosianOrder) :
    icosianModuloTwoQuotient (Ideal.Quotient.mk _ x)=icosianModuloTwo x := rfl

end Atlas.Algebra

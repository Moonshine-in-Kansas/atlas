import Atlas.Conway.EisensteinStandardFrame
import Atlas.Conway.EisensteinProjectiveModel
import Mathlib.GroupTheory.GroupAction.Quotient

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Lattices

/-- Orbit-stabilizer supplies the full Hermitian-group order once actual frame
transitivity has been proved. The transitivity premise is deliberately explicit. -/
theorem eisensteinHermitian_order_of_transitive
    (htrans : MulAction.IsPretransitive eisensteinHermitianGroup EisensteinFrame) :
    Nat.card eisensteinHermitianGroup=2690072985600 := by
  letI := htrans
  have ho : Nat.card (MulAction.orbit eisensteinHermitianGroup eisensteinStandardFrame)=232960 := by
    rw [MulAction.orbit_eq_univ,Nat.card_congr (Equiv.Set.univ EisensteinFrame),eisensteinFrame_card]
  have h := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup eisensteinHermitianGroup eisensteinStandardFrame)
  rw [Nat.card_prod,ho,eisensteinStandardFrame_stabilizer_order] at h
  exact h.symm

/-- Transport the same conditional order to the actual centralizer inside Co0. -/
theorem eisensteinCentralizer_order_of_transitive
    (htrans : MulAction.IsPretransitive eisensteinHermitianGroup EisensteinFrame) :
    Nat.card eisensteinCentralizer=2690072985600 := by
  rw [← Nat.card_congr eisensteinCentralizerEquiv.toEquiv]
  exact eisensteinHermitian_order_of_transitive htrans

/-- Divide by the actual six scalar isometries; no assertion identifying the
scalar subgroup with the entire center is needed for this conditional order. -/
theorem eisensteinProjective_order_of_transitive
    (htrans : MulAction.IsPretransitive eisensteinHermitianGroup EisensteinFrame) :
    Nat.card EisensteinProjectiveModel=448345497600 := by
  have h := eisensteinCentralizerScalars.card_eq_card_quotient_mul_card_subgroup
  rw [eisensteinCentralizer_order_of_transitive htrans,eisensteinCentralizerScalars_order] at h
  change 2690072985600=Nat.card EisensteinProjectiveModel*6 at h
  omega

theorem eisensteinHermitianQuotient_order_of_transitive
    (htrans : MulAction.IsPretransitive eisensteinHermitianGroup EisensteinFrame) :
    Nat.card EisensteinHermitianQuotient=448345497600 := by
  rw [Nat.card_congr eisensteinProjectiveComparison.toEquiv]
  exact eisensteinProjective_order_of_transitive htrans

end Atlas.Conway

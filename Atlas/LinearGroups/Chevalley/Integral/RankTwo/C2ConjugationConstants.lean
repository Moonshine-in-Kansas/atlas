import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2IntegerTemplate
/-! Kernel-checked finite integral conjugation identities. These connect the polynomial
Z and W templates to Weyl conjugates; they are not standalone group recognition. -/
namespace Atlas.Chevalley.Integral.RankTwo.C2IntegerTemplate
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem na_mul_naInv : na * naInv = 1 := by decide
theorem naInv_mul_na : naInv * na = 1 := by decide
theorem nb_mul_nbInv : nb * nbInv = 1 := by decide
theorem nbInv_mul_nb : nbInv * nb = 1 := by decide

theorem nb_ea_nbInv : nb * ea * nbInv = za := by decide
theorem nb_ea2_nbInv : nb * ea2 * nbInv = za2 := by decide
theorem na_eb_naInv : na * eb * naInv = wb := by decide
theorem na_eb2_naInv : na * eb2 * naInv = wb2 := by decide

end Atlas.Chevalley.Integral.RankTwo.C2IntegerTemplate

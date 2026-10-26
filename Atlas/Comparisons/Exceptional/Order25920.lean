import Atlas.Comparisons.Exceptional.E6.TernaryImage
import Atlas.Comparisons.LowRank.FieldTransport
import Atlas.Comparisons.Classical.Orthogonal
import Atlas.LinearGroups.Symplectic.FieldTransport

/-! The exceptional order-25920 isomorphism between the actual unitary and
symplectic models, with field transport and the retained low-rank companions. -/
noncomputable section
namespace Atlas.Comparisons.Exceptional
open Atlas.Comparisons.E6Lattice

variable {K : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K]

/-- Binary and ternary reduction of the same positive integral E6 Weyl group. -/
def psu4BinaryEquivPSp4Ternary (hdeg : Module.finrank (ZMod 2) K = 2) :
    Atlas.Unitary.PSU (ZMod 2) K 4 hdeg ≃* Atlas.Symplectic.PSp 2 (ZMod 3) :=
  (positiveWeylUnitaryEquiv hdeg).symm.trans positiveWeylSymplecticEquiv

section Transport
variable {F L T : Type*} [Field F] [Field L] [Field T]
  [Finite F] [Finite L] [Finite T] [Algebra F L]

def order25920TernaryFieldEquiv (hT : Nat.card T = 3) : ZMod 3 ≃+* T := by
  letI := Fintype.ofFinite T
  apply FiniteField.ringEquivOfCardEq
  simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hT.symm

/-- Any presentations of the binary quadratic extension and the ternary field. -/
def psu4Card2EquivPSp4Card3 (hdeg : Module.finrank F L = 2)
    (hF : Nat.card F = 2) (hT : Nat.card T = 3) :
    Atlas.Unitary.PSU F L 4 hdeg ≃* Atlas.Symplectic.PSp 2 T :=
  (Atlas.Unitary.projectiveUnitaryEquivOfBaseCardEq hdeg
    Atlas.Unitary.OrderChecks.binary_degree (by simpa only [Nat.card_zmod] using hF) 4).trans
      ((psu4BinaryEquivPSp4Ternary Atlas.Unitary.OrderChecks.binary_degree).trans
        (Atlas.Symplectic.fieldEquivPSp (order25920TernaryFieldEquiv hT)))

/-- The retained minus/unitary exterior-square map is used literally. -/
def dMinus3Card2EquivPSp4Card3 (hdeg : Module.finrank F L = 2)
    (hF : Nat.card F = 2) (hT : Nat.card T = 3) :
    Atlas.Orthogonal.DMinus 3 F L hdeg ≃* Atlas.Symplectic.PSp 2 T :=
  (Atlas.Comparisons.Classical.dMinusThreeEquivUnitary hdeg).trans
    (psu4Card2EquivPSp4Card3 hdeg hF hT)

/-- The companion B2 comparison uses the retained B2/C2 map. -/
def psu4Card2EquivB2Card3 (hdeg : Module.finrank F L = 2)
    (hF : Nat.card F = 2) (hT : Nat.card T = 3) :
    Atlas.Unitary.PSU F L 4 hdeg ≃*
      Atlas.Orthogonal.ProjectiveElementary (Atlas.Orthogonal.formB 2 T) :=
  (psu4Card2EquivPSp4Card3 hdeg hF hT).trans
    Atlas.Comparisons.Classical.b2EquivC2.symm

theorem dMinus3Card2EquivPSp4Card3_coherence (hdeg : Module.finrank F L = 2)
    (hF : Nat.card F = 2) (hT : Nat.card T = 3)
    (g : Atlas.Orthogonal.DMinus 3 F L hdeg) :
    dMinus3Card2EquivPSp4Card3 hdeg hF hT g =
      psu4Card2EquivPSp4Card3 hdeg hF hT
        (Atlas.Comparisons.Classical.dMinusThreeEquivUnitary hdeg g) := rfl

theorem psu4Card2EquivB2Card3_coherence (hdeg : Module.finrank F L = 2)
    (hF : Nat.card F = 2) (hT : Nat.card T = 3) (g : Atlas.Unitary.PSU F L 4 hdeg) :
    Atlas.Comparisons.Classical.b2EquivC2 (psu4Card2EquivB2Card3 hdeg hF hT g) =
      psu4Card2EquivPSp4Card3 hdeg hF hT g :=
  Atlas.Comparisons.Classical.b2EquivC2.apply_symm_apply _

end Transport
end Atlas.Comparisons.Exceptional

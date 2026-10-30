import FamilyWork.E6WeightedWeylSum
import FamilyWork.E6WeightedLength
import FamilyWork.FixedWeylIdentification
import FamilyWork.FixedBruhat

/-! Closed order of the literal simply connected graph--Frobenius fixed group.
The fixed Bruhat sum is transported through the actual faithful Weyl equivalence
and evaluated with the proved unequal root weights. No quotient, center or
simplicity assertion is made. Source only; verification is separate. -/

noncomputable section
namespace Atlas.Chevalley.TwistedE6.ClosedOrder
open Classical RootData F4ActionAdapter F4RootWeights FoldedWeylIdentification
  E6WeightedLength

local instance : Fintype F4Weyl := Fintype.ofFinite _

/-- Transport the exact index subtype and exact exponent of the audited fixed
Bruhat theorem; no abstract recognition or carrier replacement is involved. -/
theorem diagramFixedWeylSum_eq_f4 (q : ℕ) :
    (∑ w : E6DiagramFixedWeyl,
      q ^ rootWeylLength (rootDatum .E6).pairing (rootDatum .E6).base w.val) =
      ∑ w : F4Weyl, q ^ f4WeightedInversions w := by
  calc
    _ = ∑ w : E6DiagramFixedWeyl,
        q ^ f4WeightedInversions (fixedBruhatIndexEquivF4 w) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact congrArg (fun n : ℕ => q ^ n) (fixedBruhatIndex_length_eq_weighted w)
    _ = _ := fixedBruhatIndexEquivF4.sum_comp (fun w => q ^ f4WeightedInversions w)

theorem diagramFixedWeylSum (q : ℕ) :
    (∑ w : E6DiagramFixedWeyl,
      q ^ rootWeylLength (rootDatum .E6).pairing (rootDatum .E6).base w.val) =
      weightedWeylPolynomial q :=
  (diagramFixedWeylSum_eq_f4 q).trans (f4WeightedWeylSum q)

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Closed order of the existing simply connected E6 graph--Frobenius fixed
subgroup over a finite quadratic extension. In particular q = 2 is included. -/
theorem companionFixedSubgroup_card (hdeg : Module.finrank F K = 2) :
    Nat.card (companionFixedSubgroup F K) =
      Nat.card F ^ 36 * (Nat.card F ^ 12 - 1) * (Nat.card F ^ 9 + 1) *
        (Nat.card F ^ 8 - 1) * (Nat.card F ^ 6 - 1) *
        (Nat.card F ^ 5 + 1) * (Nat.card F ^ 2 - 1) := by
  rw [companionFixedSubgroup_card_weightedSum F K hdeg, diagramFixedWeylSum]
  exact weightedWeylPolynomial_bruhat (Nat.card F) Nat.card_pos

end Atlas.Chevalley.TwistedE6.ClosedOrder

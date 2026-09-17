import Atlas.LinearGroups.Orthogonal.ProjectiveElementary
import Atlas.LinearGroups.Orthogonal.EvenGeneration
import Atlas.LinearGroups.Orthogonal.FullOrder

/-! # The actual scalar quotient in characteristic two -/
noncomputable section
namespace Atlas.Orthogonal
variable {F V : Type*} [Field F] [CharP F 2] [AddCommGroup V] [Module F V]

/-- In characteristic two every scalar isometry with square one is the identity. -/
theorem even_elementaryScalar_eq_bot (Q : QuadraticForm F V) :
    elementaryScalarSubgroup Q = ⊥ := by
  apply bot_unique
  rintro g ⟨c, hc, hg⟩
  have hc1 : c = 1 := by
    rcases sq_eq_one_iff.mp hc with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  change g = 1
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val.val x = x
  rw [hg, hc1, one_smul]

def evenProjectiveElementaryEquiv (Q : QuadraticForm F V) :
    ProjectiveElementary Q ≃* elementarySubgroup Q :=
  (QuotientGroup.quotientMulEquivOfEq (even_elementaryScalar_eq_bot Q)).trans
    QuotientGroup.quotientBot

variable {n : ℕ} [PerfectRing F 2]

def evenElementaryBEquivFull : elementarySubgroup (formB n F) ≃* O_B n F :=
  (MulEquiv.subgroupCongr even_elementary_eq_top).trans Subgroup.topEquiv

def evenProjectiveBEquivFull : ProjectiveElementary (formB n F) ≃* O_B n F :=
  (evenProjectiveElementaryEquiv _).trans evenElementaryBEquivFull

def evenProjectiveBEquivPSp (hn : 0 < n) :
    ProjectiveElementary (formB n F) ≃* Atlas.Symplectic.PSp n F :=
  evenProjectiveBEquivFull.trans (evenFullEquivPSp hn)

@[simp] theorem evenProjectiveBEquivFull_projection (g : elementarySubgroup (formB n F)) :
    evenProjectiveBEquivFull (projectiveElementaryMap _ g) = g.val := rfl

variable [Finite F]

theorem card_evenProjectiveB (n : ℕ) :
    Nat.card (ProjectiveElementary (formB n F)) =
      Nat.card F ^ (n*n) * ∏ i ∈ Finset.range n, (Nat.card F ^ (2*(i+1))-1) := by
  rw [Nat.card_congr evenProjectiveBEquivFull.toEquiv]
  simpa [CharTwo.two_eq_zero] using (card_fullB (F := F) n)
end Atlas.Orthogonal

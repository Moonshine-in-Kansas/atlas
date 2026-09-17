import Atlas.LinearGroups.Orthogonal.SpinorNorm

/-! # The intrinsic determinant-one spinor kernel and its quotient

Identification with elementary or derived groups remains a separate theorem.
-/
noncomputable section
namespace Atlas.Orthogonal
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)

def specialSpinorNorm : specialSubgroup Q →* Atlas.SquareClass F :=
  (spinorNorm Q hQ h2).comp (specialSubgroup Q).subtype

def specialSpinorKernel : Subgroup (specialSubgroup Q) := (specialSpinorNorm Q hQ h2).ker

instance specialSpinorKernel_normal : (specialSpinorKernel Q hQ h2).Normal :=
  inferInstanceAs (specialSpinorNorm Q hQ h2).ker.Normal

/-- Every square class is realized by two reflections if all nonzero values are represented. -/
theorem specialSpinorNorm_surjective
    (hrep : ∀ c : F, c ≠ 0 → ∃ a : V, Q a = c) :
    Function.Surjective (specialSpinorNorm Q hQ h2) := by
  intro c
  obtain ⟨t, rfl⟩ := Atlas.squareClass_surjective F c
  obtain ⟨a, ha⟩ := hrep t.val t.ne_zero
  obtain ⟨b, hb⟩ := hrep 1 one_ne_zero
  have ha' : Q a ≠ 0 := ha ▸ t.ne_zero
  have hb' : Q b ≠ 0 := hb ▸ one_ne_zero
  let r := reflectionElement Q a ha' * reflectionElement Q b hb'
  have hr : r ∈ specialSubgroup Q := by
    change determinant Q r = 1
    dsimp [r]
    rw [map_mul, reflectionElement_determinant, reflectionElement_determinant, neg_mul_neg, one_mul]
  refine ⟨⟨r, hr⟩, ?_⟩
  change spinorNorm Q hQ h2 r = Atlas.squareClass F t
  dsimp [r]
  rw [map_mul, spinorNorm_reflection, spinorNorm_reflection]
  have he : Units.mk0 (Q a) ha' = t := Units.ext ha
  have he' : Units.mk0 (Q b) hb' = 1 := Units.ext hb
  rw [he, he', map_one, mul_one]

/-- The actual quotient by the restricted spinor kernel is the field square-class group. -/
def specialSpinorQuotientEquiv
    (hrep : ∀ c : F, c ≠ 0 → ∃ a : V, Q a = c) :
    (specialSubgroup Q ⧸ specialSpinorKernel Q hQ h2) ≃* Atlas.SquareClass F :=
  QuotientGroup.quotientKerEquivOfSurjective (specialSpinorNorm Q hQ h2)
    (specialSpinorNorm_surjective Q hQ h2 hrep)

/-- Over a finite odd-characteristic field, the restricted spinor kernel has index two. -/
theorem card_specialSpinorKernel_mul_two [Finite F]
    (hrep : ∀ c : F, c ≠ 0 → ∃ a : V, Q a = c) :
    Nat.card (specialSpinorKernel Q hQ h2) * 2 = Nat.card (specialSubgroup Q) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (specialSpinorKernel Q hQ h2)
  have he := Nat.card_congr (specialSpinorQuotientEquiv Q hQ h2 hrep).toEquiv
  rw [he, Atlas.card_squareClass, if_neg h2] at h
  exact (mul_comm _ _).trans h.symm

end Atlas.Orthogonal

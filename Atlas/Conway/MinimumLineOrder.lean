import Atlas.Conway.AntipodalStabilizer
import Atlas.Conway.DerivedCrossTransitivity

noncomputable section
set_option maxRecDepth 10000
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

/-- Intrinsic antipodal lines represented by norm-four vectors. -/
def MinimumLines := {l : LeechAntipodalLine // ∃ x : LeechShell 4, antipodalLine x.val = l}

theorem minimum_line_orbit (x : LeechShell 4) :
    MulAction.orbit LeechCentralQuotient (antipodalLine x.val) =
      {l | ∃ y : LeechShell 4, antipodalLine y.val = l} := by
  ext l
  constructor
  · rintro ⟨q,rfl⟩
    obtain ⟨g,rfl⟩ := leechCentralProjection_surjective q
    exact ⟨g • x, (projection_antipodalLine g x.val).symm⟩
  · rintro ⟨y,rfl⟩
    letI := full_minimum_pretransitive
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq LeechIsometryGroup x y
    refine ⟨leechCentralProjection g,?_⟩
    exact (projection_antipodalLine g x.val).trans
      (congrArg antipodalLine (congrArg Subtype.val hg))

def minimumLineOrbitEquiv (x : LeechShell 4) :
    MulAction.orbit LeechCentralQuotient (antipodalLine x.val) ≃ MinimumLines :=
  Equiv.setCongr (minimum_line_orbit x)

theorem minimum_line_stabilizer_order (x : LeechShell 4) :
    Nat.card (MulAction.stabilizer LeechCentralQuotient (antipodalLine x.val)) =
      42305421312000 := by
  rw [← Nat.card_congr (vectorAntipodalStabilizerEquiv x.val (minimum_vector_ne_zero x)).toEquiv]
  exact minimum_vector_stabilizer_order x

theorem minimum_line_orbit_stabilizer (x : LeechShell 4) :
    Nat.card MinimumLines * Nat.card (fullVectorStabilizer x.val) =
      Nat.card LeechCentralQuotient := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    LeechCentralQuotient (antipodalLine x.val))
  rw [Nat.card_prod,Nat.card_congr (minimumLineOrbitEquiv x),
    ← Nat.card_congr (vectorAntipodalStabilizerEquiv x.val (minimum_vector_ne_zero x)).toEquiv] at h
  exact h

theorem minimum_lines_card : Nat.card MinimumLines = 98280 := by
  let x : LeechShell 4 := ⟨minimumPairPlus ((0,0),0) ((0,0),1),
    minimumPairPlus_norm _ _ (by decide)⟩
  have h := minimum_line_orbit_stabilizer x
  rw [minimum_vector_stabilizer_order,leechCentralQuotient_order] at h
  apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 42305421312000)
  exact h.trans (by norm_num)

theorem minimum_antipodal_index (x : LeechShell 4) :
    (MulAction.stabilizer LeechCentralQuotient (antipodalLine x.val)).index = 98280 := by
  change Nat.card (LeechCentralQuotient ⧸ MulAction.stabilizer LeechCentralQuotient (antipodalLine x.val)) = 98280
  rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer
    LeechCentralQuotient (antipodalLine x.val)),Nat.card_congr (minimumLineOrbitEquiv x)]
  exact minimum_lines_card

end Atlas.Conway

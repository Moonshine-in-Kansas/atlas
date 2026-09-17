import Atlas.Combinatorics.BlockExtensionCount
import Atlas.Codes.WittDesign

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Combinatorics

/-- Number of retained Golay octads through a specified marked subset. -/
def octadReplication (T : Finset Omega) : ℕ :=
  (octads.filter (fun O => T ⊆ O)).card

theorem octadReplication_five (T : Finset Omega) (hT : T.card = 5) :
    octadReplication T = 1 := by
  classical
  obtain ⟨O,hO,hu⟩ := octad_steiner T hT
  have he : octads.filter (fun O => T ⊆ O) = {O} := by
    ext D
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · exact hu D
    · rintro rfl
      exact hO
  simp [octadReplication,he]

private theorem replication_step (s l : ℕ)
    (h : ∀ T : Finset Omega, T.card = s+1 → octadReplication T = l)
    (T : Finset Omega) (hT : T.card = s) :
    octadReplication T * (8-s) = (24-s)*l := by
  have hh := block_extension_count octads 8 l T
    (fun O hO => octad_size O hO) (fun x hx => h (insert x T) (by simp [hx,hT]))
  simpa only [octadReplication,hT,show Fintype.card Omega = 24 from rfl] using hh

theorem octadReplication_four (T : Finset Omega) (hT : T.card = 4) :
    octadReplication T = 5 := by
  have h := replication_step 4 1 octadReplication_five T hT
  omega

theorem octadReplication_three (T : Finset Omega) (hT : T.card = 3) :
    octadReplication T = 21 := by
  have h := replication_step 3 5 octadReplication_four T hT
  omega

theorem octadReplication_two (T : Finset Omega) (hT : T.card = 2) :
    octadReplication T = 77 := by
  have h := replication_step 2 21 octadReplication_three T hT
  omega

theorem octadReplication_one (T : Finset Omega) (hT : T.card = 1) :
    octadReplication T = 253 := by
  have h := replication_step 1 77 octadReplication_two T hT
  omega

theorem octadReplication_zero (T : Finset Omega) (hT : T.card = 0) :
    octadReplication T = 759 := by
  have h := replication_step 0 253 octadReplication_one T hT
  omega

/-- The full replication parameter formula, on the original marked Witt design. -/
theorem octadReplication_formula (T : Finset Omega) (hT : T.card ≤ 5) :
    octadReplication T = (24-T.card).choose (5-T.card) / (8-T.card).choose (5-T.card) := by
  have hc : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 ∨ T.card = 3 ∨ T.card = 4 ∨ T.card = 5 := by omega
  rcases hc with h | h | h | h | h | h
  · rw [octadReplication_zero T h,h]; norm_num [Nat.choose]
  · rw [octadReplication_one T h,h]; norm_num [Nat.choose]
  · rw [octadReplication_two T h,h]; norm_num [Nat.choose]
  · rw [octadReplication_three T h,h]; norm_num [Nat.choose]
  · rw [octadReplication_four T h,h]; norm_num [Nat.choose]
  · rw [octadReplication_five T h,h]; norm_num [Nat.choose]

end Atlas.Fischer

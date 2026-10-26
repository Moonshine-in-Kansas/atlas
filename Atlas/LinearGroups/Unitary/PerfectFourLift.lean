import Atlas.LinearGroups.Unitary.GenerationFourLift
import Atlas.LinearGroups.Unitary.PerfectHigher

/-! Lifting a verified four-dimensional generation/perfectness base to all
higher dimensions, including the binary-field family. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem special_add_four_perfect_of_four (hdeg : Module.finrank F K = 2)
    (hfour : transvectionGenerated hdeg (n := 4) = ⊤)
    [Group.IsPerfect (SU F K 4 hdeg)] (k : ℕ) :
    Group.IsPerfect (SU F K (4+k) hdeg) := by
  induction k with
  | zero => infer_instance
  | succ k ih =>
    let := ih
    have hex := exists_nonzero_isotropic_add_three hdeg (k+1)
    rw [show 3+(k+1) = 4+k by omega] at hex
    obtain ⟨v,hv,hvv⟩ := hex
    exact special_succ_perfect_of_generated hdeg v hv hvv
      (transvectionGenerated_add_four_eq_top_of_four hdeg hfour (k+1))

theorem special_perfect_of_four (hdeg : Module.finrank F K = 2)
    (hfour : transvectionGenerated hdeg (n := 4) = ⊤)
    [Group.IsPerfect (SU F K 4 hdeg)] {n : ℕ} (hn : 4 ≤ n) :
    Group.IsPerfect (SU F K n hdeg) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  exact special_add_four_perfect_of_four hdeg hfour k

theorem projective_perfect_of_four (hdeg : Module.finrank F K = 2)
    (hfour : transvectionGenerated hdeg (n := 4) = ⊤)
    [Group.IsPerfect (SU F K 4 hdeg)] {n : ℕ} (hn : 4 ≤ n) :
    Group.IsPerfect (PSU F K n hdeg) := by
  let := special_perfect_of_four hdeg hfour hn
  infer_instance
end Atlas.Unitary

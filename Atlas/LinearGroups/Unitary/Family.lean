import Atlas.LinearGroups.Unitary.SimplicityBinary
import Atlas.LinearGroups.Unitary.BinaryThreeException
import Atlas.LinearGroups.Unitary.RankOneGeneration
import Atlas.LinearGroups.Unitary.IsotropicCount
import Atlas.LinearGroups.Unitary.BaseFieldTransport
import Atlas.LinearGroups.Unitary.FixedPoints

/-! Exact simplicity range and uniform positive interfaces for the actual PSU family. -/
noncomputable section
namespace Atlas.Unitary
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem simple_of_good (hdeg : Module.finrank F K = 2) {n : ℕ} (hg : Good n (Nat.card F)) :
    IsSimpleGroup (PSU F K n hdeg) := by
  obtain ⟨hn,h2,h3,h32⟩ := hg
  by_cases he : n = 2
  · subst n
    apply (psu_two_simple_iff hdeg).mpr
    exact ⟨fun h => h2 (by simp [h]), fun h => h3 (by simp [h])⟩
  have hn3 : 3 ≤ n := by omega
  by_cases hq : Nat.card F = 2
  · have hn4 : 4 ≤ n := by
      by_contra h
      have : n = 3 := by omega
      exact h32 (by simp [this,hq])
    exact binary_projective_simple hdeg hq hn4
  · have hcard : 1 < Nat.card F := Finite.one_lt_card
    exact projective_simple_of_three_le hdeg (by omega) hn3

theorem simple_iff_good (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 2 ≤ n) :
    IsSimpleGroup (PSU F K n hdeg) ↔ Good n (Nat.card F) := by
  constructor
  · intro hs
    refine ⟨hn, ?_, ?_, ?_⟩
    · intro he
      obtain ⟨rfl,hq⟩ := Prod.mk.inj he
      exact psu_two_binary_not_simple hdeg hq hs
    · intro he
      obtain ⟨rfl,hq⟩ := Prod.mk.inj he
      exact psu_two_ternary_not_simple hdeg hq hs
    · intro he
      obtain ⟨rfl,hq⟩ := Prod.mk.inj he
      exact projective_three_binary_not_simple hdeg hq hs
  · exact simple_of_good hdeg

theorem noncommutative_of_good (hdeg : Module.finrank F K = 2) {n : ℕ}
    (hg : Good n (Nat.card F)) : ¬ IsMulCommutative (PSU F K n hdeg) := by
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨hn,h2,h3,h32⟩ := hg
  by_cases he : n = 2
  · subst n
    have hq2 : Nat.card F ≠ 2 := fun h => h2 (by simp [h])
    have hq3 : Nat.card F ≠ 3 := fun h => h3 (by simp [h])
    exact psu_two_noncommutative hdeg (by omega)
  by_cases hq : Nat.card F = 2
  · have hn4 : 4 ≤ n := by
      by_contra h
      have : n = 3 := by omega
      exact h32 (by simp [this,hq])
    exact binary_projective_noncommutative hdeg hq hn4
  · exact projective_noncommutative_of_three_le hdeg (by omega) (by omega)

theorem special_perfect_of_good (hdeg : Module.finrank F K = 2) {n : ℕ}
    (hg : Good n (Nat.card F)) : Group.IsPerfect (SU F K n hdeg) := by
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨hn,h2,h3,h32⟩ := hg
  by_cases he : n = 2
  · subst n
    have hq2 : Nat.card F ≠ 2 := fun h => h2 (by simp [h])
    have hq3 : Nat.card F ≠ 3 := fun h => h3 (by simp [h])
    exact special_two_perfect hdeg (by omega)
  by_cases hq : Nat.card F = 2
  · have hn4 : 4 ≤ n := by
      by_contra h
      have : n = 3 := by omega
      exact h32 (by simp [this,hq])
    exact binary_special_perfect hdeg hq hn4
  · exact special_perfect_of_three_le hdeg (by omega) (by omega)

theorem projective_perfect_of_good (hdeg : Module.finrank F K = 2) {n : ℕ}
    (hg : Good n (Nat.card F)) : Group.IsPerfect (PSU F K n hdeg) := by
  letI := special_perfect_of_good hdeg hg
  infer_instance

theorem transvectionGenerated_eq_top_of_good (hdeg : Module.finrank F K = 2) {n : ℕ}
    (hg : Good n (Nat.card F)) : transvectionGenerated hdeg (n := n) = ⊤ := by
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨hn,h2,h3,h32⟩ := hg
  by_cases he : n = 2
  · subst n
    have hq2 : Nat.card F ≠ 2 := fun h => h2 (by simp [h])
    have hq3 : Nat.card F ≠ 3 := fun h => h3 (by simp [h])
    exact transvectionGenerated_two_eq_top_of_four_le hdeg (by omega)
  by_cases hq : Nat.card F = 2
  · have hn4 : 4 ≤ n := by
      by_contra h
      have : n = 3 := by omega
      exact h32 (by simp [this,hq])
    exact binary_transvectionGenerated_eq_top hdeg hq hn4
  · exact transvectionGenerated_eq_top_of_three_le hdeg (by omega) (by omega)

theorem nonempty_isotropicPoints (hdeg : Module.finrank F K = 2) {n : ℕ} (hn : 2 ≤ n) :
    Nonempty (IsotropicPoints F K n) := by
  by_cases he : n = 2
  · subst n
    obtain ⟨a,b,ha,hb⟩ := exists_witt_parameters hdeg
    let v : Fin 2 → K := ![1,a]
    have hv : v ≠ 0 := by intro he; have := congrFun he 0; simpa [v] using this
    exact ⟨isotropicPoint v hv (by simp [v,hermitian,Fin.sum_univ_succ,ha])⟩
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
    obtain ⟨v,hv,hvv⟩ := exists_nonzero_isotropic_add_three hdeg k
    exact ⟨isotropicPoint v hv hvv⟩

theorem isotropic_primitive (hdeg : Module.finrank F K = 2) {n : ℕ} (hn : 2 ≤ n) :
    letI := isotropicAction hdeg (show 0 < n by omega)
    MulAction.IsPreprimitive (PSU F K n hdeg) (IsotropicPoints F K n) := by
  obtain ⟨p⟩ := nonempty_isotropicPoints hdeg hn
  exact projective_isotropic_preprimitive hdeg (by omega) p
end Atlas.Unitary

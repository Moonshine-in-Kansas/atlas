import Atlas.LinearGroups.Unitary.BinaryThreeMonomial
import Atlas.LinearGroups.Unitary.BinaryFourierModel
import Mathlib.GroupTheory.Subgroup.Simple

/-! Explicit proper nontrivial normal subgroup in the actual PSU₃(2) model. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def binaryThreeNormal (hdeg : Module.finrank F K = 2) : Subgroup (PSU F K 3 hdeg) :=
  (transvectionGenerated hdeg (n := 3)).map (projection F K 3 hdeg)

instance binaryThreeNormal_normal (hdeg : Module.finrank F K = 2) :
    (binaryThreeNormal hdeg).Normal :=
  (inferInstance : (transvectionGenerated hdeg (n := 3)).Normal).map
    (projection F K 3 hdeg) (projection_surjective F K 3 hdeg)

theorem binaryThreeNormal_ne_bot (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2) :
    binaryThreeNormal hdeg ≠ ⊥ := by
  letI := binary_charP hdeg hq
  let v : Fin 3 → K := ![1,1,0]
  have hv : v ≠ 0 := by intro he; have := congrFun he 0; simpa [v] using this
  have hvv : hermitian F K v v = 0 := by
    simp [v,hermitian,Fin.sum_univ_three,CharTwo.add_self_eq_zero]
  let p := isotropicPoint v hv hvv
  have hle : projectivePointTransvections hdeg p ≤ binaryThreeNormal hdeg :=
    Subgroup.map_mono (pointTransvections_le_generated hdeg p)
  intro he
  rw [he] at hle
  have hp := bot_unique hle
  have hc := card_projectivePointTransvections hdeg (by decide : 0 < 3) p
  rw [hp,hq] at hc
  simpa using hc

theorem binaryThreeNormal_ne_top (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2) :
    binaryThreeNormal hdeg ≠ ⊤ := by
  letI := binary_charP hdeg hq
  obtain ⟨c,hc⟩ := exists_binary_primitive hdeg hq
  intro he
  have ht : transvectionGenerated hdeg (n := 3) ⊔ Subgroup.center (SU F K 3 hdeg) = ⊤ := by
    rw [← projection_kernel F K 3 hdeg, ← Subgroup.comap_map_eq]
    change (binaryThreeNormal hdeg).comap (projection F K 3 hdeg) = ⊤
    rw [he, Subgroup.comap_top]
  have hle := sup_le (binary_three_generated_le_coordinateStabilizer hdeg hq)
    (center_le_coordinateStabilizer hdeg (n := 3) (by decide))
  rw [ht] at hle
  exact binaryFourier_not_coordinateStabilizer hdeg hq c hc (hle (Subgroup.mem_top _))

theorem projective_three_binary_not_simple (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) : ¬ IsSimpleGroup (PSU F K 3 hdeg) := by
  intro hs
  letI := hs
  rcases (inferInstance : (binaryThreeNormal hdeg).Normal).eq_bot_or_eq_top with h | h
  · exact binaryThreeNormal_ne_bot hdeg hq h
  · exact binaryThreeNormal_ne_top hdeg hq h
end Atlas.Unitary

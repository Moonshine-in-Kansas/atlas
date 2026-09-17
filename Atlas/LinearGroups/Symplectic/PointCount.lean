import Atlas.LinearGroups.Symplectic.PointOrbits
import Atlas.LinearAlgebra.ProjectiveSubmodule
import Atlas.LinearAlgebra.LinearFunctionalFiber
import Mathlib.LinearAlgebra.Projectivization.Cardinality

noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F] [Finite F]

/-- Cardinality of the actual projective point set, independently of group order. -/
theorem card_points : Nat.card (Points n F) = (Nat.card F^(2*n)-1)/(Nat.card F-1) := by
  rw [Projectivization.card'',Module.natCard_eq_pow_finrank (K := F)]
  simp [Vector,Index,two_mul]

/-- The entire perp is the projectivization of an actual hyperplane kernel. -/
def perpendicularPointsEquiv (p : Points n F) :
    (ℙ F (form p.rep).ker) ≃ {q : Points n F // Orthogonal p q} :=
  Atlas.LinearAlgebra.projectiveSubmoduleEquiv (form p.rep).ker

theorem card_perpendicular_points (p : Points n F) :
    Nat.card {q : Points n F // Orthogonal p q} =
      (Nat.card F^(2*n-1)-1)/(Nat.card F-1) := by
  rw [← Nat.card_congr (perpendicularPointsEquiv p),Projectivization.card'']
  obtain ⟨v,hv⟩ := Atlas.AlternatingForm.exists_partner form form_nondegenerate p.rep_nonzero
  have hk : Nat.card (form p.rep).ker = Nat.card F^(2*n-1) := by
    change Nat.card {x : Vector n F // form p.rep x=0} = _
    have h := Atlas.LinearFunctional.card_fiber (form p.rep) v hv 0
    simpa [Vector,Index,two_mul] using h
  rw [hk]

theorem card_suborbit_zero (p : Points n F) :
    Nat.card {q : Points n F // suborbitIndex p q=0} = 1 := by
  classical
  have he : {q : Points n F | suborbitIndex p q=0} = {p} := by
    ext q
    by_cases hq : q=p <;> by_cases ho : Orthogonal p q <;> simp [suborbitIndex,hq,ho]
  calc
    _ = Nat.card ↥({p} : Set (Points n F)) := Nat.card_congr (Equiv.setCongr he)
    _ = 1 := by simp

theorem suborbitIndex_eq_one_iff (p q : Points n F) :
    suborbitIndex p q=1 ↔ Orthogonal p q ∧ q ≠ p := by
  classical
  by_cases hq : q=p <;> by_cases ho : Orthogonal p q <;> simp [suborbitIndex,hq,ho]

theorem suborbitIndex_eq_two_iff (p q : Points n F) :
    suborbitIndex p q=2 ↔ ¬ Orthogonal p q := by
  classical
  by_cases hq : q=p
  · subst q; simp
  · by_cases ho : Orthogonal p q <;> simp [suborbitIndex,hq,ho]

theorem card_suborbit_one (p : Points n F) :
    Nat.card {q : Points n F // suborbitIndex p q=1} =
      Nat.card {q : Points n F // Orthogonal p q} - 1 := by
  classical
  let a : {q : Points n F // Orthogonal p q} := ⟨p,orthogonal_self p⟩
  let eqv : {q : Points n F // suborbitIndex p q=1} ≃
      {q : {q : Points n F // Orthogonal p q} // q ≠ a} :=
    { toFun := fun q => ⟨⟨q.val,((suborbitIndex_eq_one_iff p q.val).mp q.prop).1⟩,
        fun h => ((suborbitIndex_eq_one_iff p q.val).mp q.prop).2 (congrArg Subtype.val h)⟩
      invFun := fun q => ⟨q.val.val,(suborbitIndex_eq_one_iff p q.val.val).mpr
        ⟨q.val.prop,fun h => q.prop (Subtype.ext h)⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let := Fintype.ofFinite {q : Points n F // Orthogonal p q}
  have hu : Fintype.card {x : {q : Points n F // Orthogonal p q} // x=a} = 1 :=
    Fintype.card_unique
  rw [Nat.card_congr eqv,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
    hu,Nat.card_eq_fintype_card]

theorem card_suborbit_two (p : Points n F) :
    Nat.card {q : Points n F // suborbitIndex p q=2} =
      Nat.card (Points n F) - Nat.card {q : Points n F // Orthogonal p q} := by
  classical
  let := Fintype.ofFinite (Points n F)
  let eqv := Equiv.subtypeEquivRight (suborbitIndex_eq_two_iff p)
  rw [Nat.card_congr eqv,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
    Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]

def pointSum (q m : ℕ) : ℕ := ∑ i ∈ Finset.range m,q^i

theorem card_points_sum : Nat.card (Points n F) = pointSum (Nat.card F) (2*n) := by
  apply Projectivization.card_of_finrank
  simp [Vector,Index,two_mul]

theorem card_perpendicular_points_sum (p : Points n F) :
    Nat.card {q : Points n F // Orthogonal p q} = pointSum (Nat.card F) (2*n-1) := by
  rw [← Nat.card_congr (perpendicularPointsEquiv p)]
  apply Projectivization.card_of_finrank
  obtain ⟨v,hv⟩ := Atlas.AlternatingForm.exists_partner form form_nondegenerate p.rep_nonzero
  have hr : LinearMap.range (form p.rep) = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro a
    exact ⟨a • v,by simp [map_smul,hv]⟩
  have h := (form p.rep).finrank_range_add_finrank_ker
  rw [hr,finrank_top,Module.finrank_self] at h
  have hd : Module.finrank F (Vector n F) = 2*n := by simp [Vector,Index,two_mul]
  omega

end Atlas.Symplectic


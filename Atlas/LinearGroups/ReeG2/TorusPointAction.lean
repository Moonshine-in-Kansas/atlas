import Atlas.LinearGroups.ReeG2.ProjectiveAction
import Atlas.LinearGroups.ReeG2.TorusRootAction

noncomputable section
namespace Atlas.ReeG2
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
set_option maxHeartbeats 2000000

theorem pointRight_zero_torus (m : ℕ) (l : Fˣ) :
    pointRight (torus m l) (affinePoint m 0 0 0) = affinePoint m 0 0 0 := by
  unfold pointRight affinePoint
  rw [Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
  refine ⟨Units.map (theta F m).toMonoidHom l,?_⟩
  ext i
  fin_cases i <;>
    simp [rowEquiv_apply, affineVector, rootMatrix_zero, torus, diagonalUnit,
      torusDiagonal, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Units.smul_def]

theorem pointRight_infinity_torus (m : ℕ) (l : Fˣ) :
    pointRight (torus m l) infinityPoint = infinityPoint := by
  unfold pointRight infinityPoint
  rw [Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
  refine ⟨(Units.map (theta F m).toMonoidHom l)⁻¹,?_⟩
  ext i
  fin_cases i <;>
    simp [rowEquiv_apply, infinityVector, torus, diagonalUnit,
      torusDiagonal, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Units.smul_def]

theorem pointRight_affine_torus (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (l : Fˣ) (a b c : F) :
    pointRight (torus m l) (affinePoint m a b c) =
      affinePoint m (a * (theta F m (l : F))^3 / (l : F)^2)
        (b * (l : F) / (theta F m (l : F))^3) (c / (l : F)) := by
  have ht := torus_conjugate_root m hcard l a b c
  have he : rootElement m a b c * torus m l = torus m l *
      rootElement m (a * (theta F m (l : F))^3 / (l : F)^2)
        (b * (l : F) / (theta F m (l : F))^3) (c / (l : F)) := by
    rw [← ht]
    group
  rw [← pointRight_zero_root m hcard a b c]
  change (pointRight (torus m l) ∘ pointRight (rootElement m a b c)) _ = _
  rw [← pointRight_mul,he,pointRight_mul]
  change pointRight _ (pointRight (torus m l) (affinePoint m 0 0 0)) = _
  rw [pointRight_zero_torus,pointRight_zero_root m hcard]

theorem torus_preserves_pointSet (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (l : Fˣ) {p : Projective F} (hp : p ∈ pointSet m) :
    pointRight (torus m l) p ∈ pointSet m := by
  obtain ⟨p,rfl⟩ := hp
  cases p with
  | none =>
    change pointRight (torus m l) infinityPoint ∈ pointSet m
    rw [pointRight_infinity_torus]
    exact ⟨none,rfl⟩
  | some p =>
    obtain ⟨a,b,c⟩ := p
    change pointRight (torus m l) (affinePoint m a b c) ∈ pointSet m
    rw [pointRight_affine_torus m hcard]
    exact ⟨some (_,_,_),rfl⟩
end Atlas.ReeG2

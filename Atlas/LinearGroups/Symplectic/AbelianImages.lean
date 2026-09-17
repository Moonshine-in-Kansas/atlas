import Atlas.LinearGroups.Symplectic.PerfectLarge
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.RingTheory.Fintype
import Mathlib.Algebra.CharP.CharAndCard

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F A : Type*} [Field F] [CommGroup A]

theorem abelian_transvection_images (f : Sp n F →* A)
    {u v : Vector n F} (hu : u ≠ 0) (hv : v ≠ 0) (a : F) :
    f (transvection u a) = f (transvection v a) := by
  obtain ⟨g,_,hg⟩ := exists_generated_send hu hv
  have h := congrArg f (transvection_conjugate g u a)
  simpa [hg,map_mul,map_inv,mul_comm,mul_left_comm,mul_assoc] using h

/-- An additive parameter repeated k times is k times that parameter. -/
theorem transvection_pow (v : Vector n F) (a : F) (k : ℕ) :
    transvection v a ^ k = transvection v (k • a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,ih,← transvection_add,succ_nsmul,add_comm]

theorem perfect_of_abelian_images
    (h : ∀ (v : Vector n F) (a : F), Abelianization.of (transvection v a) = 1) :
    Group.IsPerfect (Sp n F) := by
  apply perfect_of_transvections
  intro v a
  rw [← Abelianization.ker_of]
  exact h v a

end Atlas.Symplectic

import Atlas.LinearGroups.Orthogonal.EvenComparison
import Atlas.LinearGroups.Symplectic.Exceptions
import Atlas.LinearGroups.Symplectic.Noncommutative

/-! # Simplicity and perfectness of the actual B quadratic model in characteristic two -/
noncomputable section
namespace Atlas.Orthogonal
variable {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The same actual full B model has the exact finite-field C simplicity range. -/
theorem even_full_simple_iff (hn : 0 < n) :
    IsSimpleGroup (O_B n F) ↔ Atlas.Symplectic.Good n (Nat.card F) := by
  constructor
  · intro h
    letI := h
    exact (Atlas.Symplectic.simple_iff_good (F := F)).mp (evenFullEquivPSp (F := F) hn).symm.isSimpleGroup
  · intro h
    letI := (Atlas.Symplectic.simple_iff_good (F := F)).mpr h
    exact (evenFullEquivPSp (F := F) hn).isSimpleGroup

theorem even_full_perfect (h : Atlas.Symplectic.Good n (Nat.card F)) :
    Group.IsPerfect (O_B n F) := by
  letI := Atlas.Symplectic.perfect_of_good h
  exact Group.IsPerfect.ofSurjective (f := (evenFullEquivSp (n := n) (F := F)).symm.toMonoidHom)
    (evenFullEquivSp (n := n) (F := F)).symm.surjective

theorem even_full_noncommutative (h : Atlas.Symplectic.Good n (Nat.card F)) :
    ¬ IsMulCommutative (O_B n F) := by
  have hn : 0 < n := by rcases h with h | h <;> omega
  letI := Atlas.Symplectic.projective_nontrivial (F := F) hn
  letI : Nontrivial (O_B n F) := (evenFullEquivPSp (F := F) hn).symm.injective.nontrivial
  letI := even_full_perfect h
  exact Group.IsPerfect.not_isMulCommutative (O_B n F)

end Atlas.Orthogonal

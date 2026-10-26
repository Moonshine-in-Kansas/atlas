import Atlas.LinearGroups.Orthogonal.Minus.Simplicity
import Atlas.LinearGroups.Orthogonal.Minus.ProjectiveOrder
import Atlas.LinearGroups.Orthogonal.Minus.FieldTransport

/-! Stable public minus-orthogonal family. The low-rank comparisons remain separate. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Half-dimension n: actual elementary isometries modulo their scalar subgroup. -/
abbrev DMinus (n : ℕ) (F K : Type*) [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K = 2) :=
  ProjectiveElementary (form hdeg (n-1))

theorem family_finite (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Finite (DMinus n F K hdeg) := inferInstance

def orderNumerator (q n : ℕ) : ℕ :=
  q^(n*(n-1)) * (q^n+1) * ∏ i ∈ Finset.range (n-1), (q^(2*(i+1))-1)

theorem family_simple (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 4 ≤ n) :
    IsSimpleGroup (DMinus n F K hdeg) := by
  have he : n-1 = (n-4)+3 := by omega
  unfold DMinus
  rw [he]
  exact projective_simple hdeg (n-4)

theorem family_noncommutative (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 4 ≤ n) :
    ¬ IsMulCommutative (DMinus n F K hdeg) := by
  have he : n-1 = (n-4)+3 := by omega
  unfold DMinus
  rw [he]
  exact projective_noncommutative hdeg (n-4)

theorem family_order (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 3 ≤ n) :
    Nat.card (DMinus n F K hdeg) = orderNumerator (Nat.card F) n /
      Nat.gcd 4 (Nat.card F^n+1) := by
  unfold DMinus orderNumerator
  have he : n-1=(n-3)+2 := by omega
  rw [he]
  simpa only [show n-3+3=n by omega] using card_projective hdeg (n-3)

theorem family_full_order (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (O hdeg (n-1)) = 2 * orderNumerator (Nat.card F) n := by
  have he : n-1+1=n := by omega
  simpa only [orderNumerator,he,mul_assoc] using card_full hdeg (n-1)

theorem family_elementary_perfect (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 4 ≤ n) :
    Group.IsPerfect (E hdeg (n-1)) := by
  have he : n-1 = (n-4)+3 := by omega
  rw [he]
  exact elementary_perfect hdeg (n-4)

theorem family_center_scalar (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 3 ≤ n) :
    elementaryScalarSubgroup (form hdeg (n-1)) = Subgroup.center (E hdeg (n-1)) := by
  have he : n-1 = (n-3)+2 := by omega
  rw [he]
  exact center_scalar hdeg (n-3)

theorem family_projection_kernel (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 3 ≤ n) :
    (projectiveElementaryMap (form hdeg (n-1))).ker = Subgroup.center (E hdeg (n-1)) := by
  rw [projectiveElementaryMap_kernel,family_center_scalar hdeg n hn]

theorem family_faithful (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 3 ≤ n) :
    FaithfulSMul (DMinus n F K hdeg) (SingularPoints (form hdeg (n-1))) := by
  have he : n-1 = (n-3)+2 := by omega
  unfold DMinus
  rw [he]
  exact projectiveSingular_faithful_minus hdeg (n-3)

theorem family_primitive (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 4 ≤ n) :
    MulAction.IsPreprimitive (DMinus n F K hdeg) (SingularPoints (form hdeg (n-1))) := by
  have he : n-1 = (n-4)+3 := by omega
  unfold DMinus
  rw [he]
  exact projectiveSingular_primitive hdeg (n-4)

theorem family_intrinsic_odd (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 3 ≤ n)
    (h2 : (2 : F) ≠ 0) (g : O hdeg (n-1)) :
    g ∈ E hdeg (n-1) ↔ determinant (form hdeg (n-1)) g = 1 ∧
      spinorNorm (form hdeg (n-1)) (polar_nondegenerate hdeg _) h2 g = 1 := by
  have he : n-1 = (n-3)+2 := by omega
  revert g
  rw [he]
  intro g
  rw [elementary_eq_intrinsic_kernel hdeg (n-3) h2]
  rfl

theorem family_intrinsic_even [CharP F 2] (hdeg : Module.finrank F K = 2)
    (n : ℕ) (hn : 3 ≤ n) (g : O hdeg (n-1)) :
    g ∈ E hdeg (n-1) ↔ dicksonValue (form hdeg (n-1)) g = 0 := by
  have he : n-1 = (n-3)+2 := by omega
  revert g
  rw [he]
  intro g
  rw [← fullDickson_kernel_elementary hdeg (n-3)]
  rfl
end Atlas.Orthogonal.Minus

namespace Atlas.Orthogonal
/-- Public minus family, retaining its actual norm-tail scalar quotient. -/
abbrev DMinus (n : ℕ) (F K : Type*) [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K = 2) := Minus.DMinus n F K hdeg
end Atlas.Orthogonal

import Atlas.LinearGroups.SuzukiFamily.Perfect
import Atlas.LinearGroups.SuzukiFamily.PointTransitivity
import Atlas.LinearGroups.SuzukiFamily.BorelSolvable
import Atlas.GroupTheory.SolvableStabilizerSimplicity

/-! Uniform simplicity from the faithful primitive ovoid action and solvable stabilizer. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem group_nontrivial (m : ℕ) : Nontrivial (Group F m) := by
  refine ⟨⟨⟨weylElement,weylElement_mem m⟩,1,?_⟩⟩
  intro he
  have hw : (weylElement : Atlas.Symplectic.Sp 2 F)=1 := congrArg Subtype.val he
  have hp := weyl_infinity (F := F) m
  rw [hw,pointLeft_one] at hp
  exact infinity_ne_affine m 0 0 hp

theorem simple_of_large (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (hm : 1≤m) :
    IsSimpleGroup (Group F m) := by
  letI := pointAction m hcard
  letI := group_nontrivial (F := F) m
  letI := perfect_of_large m hcard hm
  letI := pointAction_preprimitive m hcard
  letI := pointAction_faithful m hcard
  letI : _root_.Group.IsSolvable (MulAction.stabilizer (Group F m) (infinityOvoid (F := F) m)) :=
    borel_solvable m hcard
  exact Atlas.GroupTheory.simple_of_perfect_quasiprimitive_solvable_stabilizer
    (infinityOvoid (F := F) m)

theorem noncommutative_of_large (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (hm : 1≤m) :
    ¬ IsMulCommutative (Group F m) := by
  letI := group_nontrivial (F := F) m
  letI := perfect_of_large m hcard hm
  exact _root_.Group.IsPerfect.not_isMulCommutative (Group F m)
end Atlas.SuzukiFamily

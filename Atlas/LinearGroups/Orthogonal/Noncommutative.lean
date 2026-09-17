import Atlas.LinearGroups.Orthogonal.ElementaryPairStandard
import Atlas.LinearGroups.Orthogonal.PerfectStable

/-! # Nontriviality and noncommutativity for actual odd intrinsic groups -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem elementary_nontrivial_of_pair_transport (Q : QuadraticForm F V)
    (e f : V) (he : Q e = 0) (hef : Q.polarBilin e f = 1)
    (ht : ∃ g : isometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val e = f) :
    Nontrivial (elementarySubgroup Q) := by
  have hne : e ≠ f := by
    intro h
    have hp : Q.polarBilin e e = 0 := by rw [polar_self, he, mul_zero]
    rw [← h, hp] at hef
    exact zero_ne_one hef
  obtain ⟨g, hg, hgf⟩ := ht
  refine ⟨⟨⟨g, hg⟩, 1, ?_⟩⟩
  intro h
  have hval := congrArg (fun k : elementarySubgroup Q => k.val.val e) h
  change g.val e = e at hval
  exact hne (hval.symm.trans hgf)

theorem elementaryB_nontrivial (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nontrivial (elementarySubgroup (formB (n+2) F)) := by
  let H := wittTwoFrameB (F := F) n
  apply elementary_nontrivial_of_pair_transport _ H.e₁ H.f₁ H.qe₁ H.pair₁
  obtain ⟨g, hg, he, _⟩ := elementaryB_pair_transport n h2 H.e₁ H.f₁ H.f₁ H.e₁
    H.qe₁ H.qf₁ H.qf₁ H.qe₁ H.pair₁ ((polar_swap _ _ _).trans H.pair₁)
  exact ⟨g, hg, he⟩

theorem elementaryD_nontrivial (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nontrivial (elementarySubgroup (formD (n+2) F)) := by
  let H := wittTwoFrameD (F := F) n
  apply elementary_nontrivial_of_pair_transport _ H.e₁ H.f₁ H.qe₁ H.pair₁
  obtain ⟨g, hg, he, _⟩ := elementaryD_pair_transport n h2 H.e₁ H.f₁ H.f₁ H.e₁
    H.qe₁ H.qf₁ H.qf₁ H.qe₁ H.pair₁ ((polar_swap _ _ _).trans H.pair₁)
  exact ⟨g, hg, he⟩

variable [Finite F]

theorem elementaryB_noncommutative_stable (n : ℕ) (h2 : (2 : F) ≠ 0) :
    ¬ IsMulCommutative (elementarySubgroup (formB (n+3) F)) := by
  letI := elementaryB_nontrivial (n+1) h2
  letI := elementaryB_perfect_stable n h2
  exact Group.IsPerfect.not_isMulCommutative _

theorem elementaryD_noncommutative_stable (n : ℕ) (h2 : (2 : F) ≠ 0) :
    ¬ IsMulCommutative (elementarySubgroup (formD (n+3) F)) := by
  letI := elementaryD_nontrivial (n+1) h2
  letI := elementaryD_perfect_stable n h2
  exact Group.IsPerfect.not_isMulCommutative _

theorem elementaryB_noncommutative_of_card_gt_three (n : ℕ) (h2 : (2 : F) ≠ 0)
    (hq : 3 < Nat.card F) : ¬ IsMulCommutative (elementarySubgroup (formB (n+2) F)) := by
  letI := elementaryB_nontrivial n h2
  letI := elementaryB_perfect_of_card_gt_three n h2 hq
  exact Group.IsPerfect.not_isMulCommutative _

theorem elementaryD_noncommutative_of_card_gt_three (n : ℕ) (h2 : (2 : F) ≠ 0)
    (hq : 3 < Nat.card F) : ¬ IsMulCommutative (elementarySubgroup (formD (n+2) F)) := by
  letI := elementaryD_nontrivial n h2
  letI := elementaryD_perfect_of_card_gt_three n h2 hq
  exact Group.IsPerfect.not_isMulCommutative _

theorem oddSpinorKernelB_noncommutative_stable (n : ℕ) (h2 : (2 : F) ≠ 0) :
    ¬ IsMulCommutative (oddSpinorKernelB (n+3) h2) := by
  letI := elementaryB_nontrivial (n+1) h2
  letI := (elementaryB_kernelEquiv (n+1) h2).toEquiv.symm.nontrivial
  letI := oddSpinorKernelB_perfect_stable n h2
  exact Group.IsPerfect.not_isMulCommutative _

theorem oddSpinorKernelD_noncommutative_stable (n : ℕ) (h2 : (2 : F) ≠ 0) :
    ¬ IsMulCommutative (oddSpinorKernelD (n+3) h2) := by
  letI := elementaryD_nontrivial (n+1) h2
  letI := (elementaryD_kernelEquiv (n+1) h2).toEquiv.symm.nontrivial
  letI := oddSpinorKernelD_perfect_stable n h2
  exact Group.IsPerfect.not_isMulCommutative _
end Atlas.Orthogonal

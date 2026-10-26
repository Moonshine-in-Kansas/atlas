import Atlas.LinearGroups.Chevalley.WeightCompanionCentralTorus

/-! UNCHECKED continuation: exact intersection of the actual companion torus
with the center. No containment of the whole center or projection kernel in
the torus is assumed or asserted. No Bruhat or adjoint injectivity premise. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical
variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) (b : P.Base)

/-- Every actual root weight belongs to the integral span of the simple ones. -/
theorem rootWeight_mem_span_simple (a : ι) :
    rootWeight P a ∈ Submodule.span ℤ
      (Set.range (fun i : b.support => rootWeight P i.val)) := by
  let F : M →ₗ[ℤ] WeightLattice P :=
    { toFun := fun x => (P.toLinearMap x).comp (P.flip.rootSpan ℤ).subtype
      map_add' := by intro x y; ext z; simp
      map_smul' := by intro t x; ext z; simp }
  have hs : Submodule.span ℤ (P.root '' (↑b.support : Set ι)) ≤
      (Submodule.span ℤ (Set.range (fun i : b.support => rootWeight P i.val))).comap F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  exact hs (b.root_mem_span_int a)

end Atlas.Chevalley.Integral.Minuscule

namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- The existing actual torus conjugation formula, accumulated over a tuple. -/
theorem adjointTorusProduct_mul_X (s : Finset b.support) (t : b.support → Rˣ)
    (i : b.support) (z : R) :
    adjointTorusProduct P b R s t * adjointX P b R i z =
      adjointX P b R i ((∏ j ∈ s, (t j) ^ b.cartanMatrix i j).val * z) *
        adjointTorusProduct P b R s t := by
  induction s using Finset.induction_on with
  | empty => simp [adjointTorusProduct]
  | @insert j s hj ih =>
    have hi : adjointTorusProduct P b R (insert j s) t =
        adjointTorus P b R j (t j) * adjointTorusProduct P b R s t := by
      unfold adjointTorusProduct
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hj]
    rw [hi, Finset.prod_insert hj, Units.val_mul]
    calc
      _ = adjointTorus P b R j (t j) *
          (adjointX P b R i ((∏ k ∈ s, (t k) ^ b.cartanMatrix i k).val * z) *
            adjointTorusProduct P b R s t) := by rw [mul_assoc, ih]
      _ = (adjointTorus P b R j (t j) *
          adjointX P b R i ((∏ k ∈ s, (t k) ^ b.cartanMatrix i k).val * z)) *
            adjointTorusProduct P b R s t := (mul_assoc _ _ _).symm
      _ = _ := by rw [adjointTorus_mul_X]; simp only [mul_assoc]

/-- A torus tuple commuting with each pinned X_i(1) already has trivial
adjoint image. Root-parameter injectivity avoids division, including at 2/3. -/
theorem adjointTorusParameters_eq_one_of_commute_simpleX
    (t : b.support → Rˣ)
    (h : ∀ i : b.support, Commute (adjointTorusParameters P b R t)
      (adjointX P b R i 1)) :
    adjointTorusParameters P b R t = 1 := by
  have hcoord (i j : b.support) :
      rootWeight P i.val (corootBasis P b j) = b.cartanMatrix i j := by
    rw [← weightCoordinates_apply, simpleRootWeight_coordinates]
  have hs (i : b.support) : weightTorusCharacter P b R t (rootWeight P i.val) = 1 := by
    have hc := adjointTorusProduct_mul_X P b R Finset.univ t i 1
    change adjointTorusParameters P b R t * adjointX P b R i 1 =
      adjointX P b R i ((∏ j : b.support, (t j) ^ b.cartanMatrix i j).val * 1) *
        adjointTorusParameters P b R t at hc
    have he := mul_right_cancel ((h i).eq.symm.trans hc)
    have hp := adjointX_injective P b R i he
    change weightTorusCharacter P b R t (rootWeight P i.val) = 1
    apply Units.ext
    simpa only [weightTorusCharacter, hcoord, Units.val_one, mul_one] using hp.symm
  have hspan : Submodule.span ℤ
      (Set.range (fun i : b.support => rootWeight P i.val)) ≤
        weightTorusCharacterKernel P b R t := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hs i
  apply (adjointTorusParameters_eq_one_iff_character P R b t).mpr
  intro a
  change weightTorusCharacter P b R t (rootWeight P a) = 1
  exact hspan (rootWeight_mem_span_simple P b a)

end Atlas.Chevalley

universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

/-- Reverse inclusion on the actual torus, with no whole-center claim. -/
theorem weightCompanion_torus_center_rho_eq_one
    (g : WeightCompanion P b O hclosed hmin R)
    (ht : g ∈ weightCompanionTorusSubgroup P b O hclosed hmin R)
    (hz : g ∈ Subgroup.center (WeightCompanion P b O hclosed hmin R)) :
    weightCompanionRho P b O hclosed hmin R g = 1 := by
  rw [weightCompanionTorusSubgroup_eq_range] at ht
  obtain ⟨t, rfl⟩ := ht
  rw [weightCompanionRho_torusParameters]
  apply adjointTorusParameters_eq_one_of_commute_simpleX P b R t
  intro i
  have he := (Subgroup.mem_center_iff.mp hz (weightCompanionX P b O hclosed hmin R i 1)).symm
  have hp := congrArg (weightCompanionRho P b O hclosed hmin R) he
  change adjointTorusParameters P b R t * adjointX P b R i 1 =
    adjointX P b R i 1 * adjointTorusParameters P b R t
  simpa only [map_mul, weightCompanionRho_torusParameters, weightCompanionRho_X] using hp

/-- The actual central part of T is exactly its intersection with ker rho. -/
theorem weightCompanion_torus_inf_center_eq_inf_kernel :
    weightCompanionTorusSubgroup P b O hclosed hmin R ⊓
        Subgroup.center (WeightCompanion P b O hclosed hmin R) =
      weightCompanionTorusSubgroup P b O hclosed hmin R ⊓
        (weightCompanionRho P b O hclosed hmin R).ker := by
  apply le_antisymm
  · rintro g ⟨ht, hz⟩
    exact ⟨ht, weightCompanion_torus_center_rho_eq_one P b O hclosed hmin R g ht hz⟩
  · rintro g ⟨ht, hk⟩
    exact ⟨ht, weightCompanion_torus_kernel_central P b O hclosed hmin R g ht hk⟩

/-- The existing character identification now describes T intersect center.
It still does not identify the whole center. -/
def weightCompanionTorusCenterCharacterEquiv
    (hspan : Submodule.span ℤ (Set.range (rootWeight P) ∪ {μ | ∃ k, μ ∈ O k}) = ⊤) :
    ↥(weightCompanionTorusSubgroup P b O hclosed hmin R ⊓
        Subgroup.center (WeightCompanion P b O hclosed hmin R)) ≃*
      (Multiplicative (WeightLattice P ⧸ rootLattice P) →* Rˣ) :=
  (MulEquiv.subgroupCongr
    (weightCompanion_torus_inf_center_eq_inf_kernel P b O hclosed hmin R)).trans
      (weightCompanionCentralTorusCharacterEquiv P b O hclosed hmin R hspan)

end Atlas.Chevalley

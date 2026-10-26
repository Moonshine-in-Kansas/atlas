import Atlas.LinearGroups.Chevalley.WeightCompanion
import Atlas.LinearGroups.Chevalley.AdjointPerfectness
/-! Actual simultaneous generator and induction laws. -/
noncomputable section
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

theorem weightCompanionX_add (i : b.support) (s t : R) :
    weightCompanionX P b O hclosed hmin R i (s+t) =
      weightCompanionX P b O hclosed hmin R i s * weightCompanionX P b O hclosed hmin R i t := by
  apply Subtype.ext
  apply Prod.ext
  · exact adjointX_add P b R i s t
  · funext a
    apply Units.ext
    exact (stringsOfWeightOrbit P (O a) (hclosed a) (hmin a)).rootMatrix_add R i.val (-1)
      (by decide) s t

theorem weightCompanionY_add (i : b.support) (s t : R) :
    weightCompanionY P b O hclosed hmin R i (s+t) =
      weightCompanionY P b O hclosed hmin R i s * weightCompanionY P b O hclosed hmin R i t := by
  apply Subtype.ext
  apply Prod.ext
  · exact adjointY_add P b R i s t
  · funext a
    apply Units.ext
    exact (stringsOfWeightOrbit P (O a) (hclosed a) (hmin a)).rootMatrix_add R i.val 1
      (by decide) s t

def weightCompanionXHom (i : b.support) : Multiplicative R →* WeightCompanion P b O hclosed hmin R where
  toFun t := weightCompanionX P b O hclosed hmin R i t.toAdd
  map_one' := by
    have h : weightCompanionX P b O hclosed hmin R i 0 * weightCompanionX P b O hclosed hmin R i 0 =
        weightCompanionX P b O hclosed hmin R i 0 := by
      simpa using (weightCompanionX_add P b O hclosed hmin R i 0 0).symm
    exact mul_eq_left.mp h
  map_mul' s t := weightCompanionX_add P b O hclosed hmin R i s.toAdd t.toAdd

def weightCompanionYHom (i : b.support) : Multiplicative R →* WeightCompanion P b O hclosed hmin R where
  toFun t := weightCompanionY P b O hclosed hmin R i t.toAdd
  map_one' := by
    have h : weightCompanionY P b O hclosed hmin R i 0 * weightCompanionY P b O hclosed hmin R i 0 =
        weightCompanionY P b O hclosed hmin R i 0 := by
      simpa using (weightCompanionY_add P b O hclosed hmin R i 0 0).symm
    exact mul_eq_left.mp h
  map_mul' s t := weightCompanionY_add P b O hclosed hmin R i s.toAdd t.toAdd

theorem weightCompanion_induction {C : WeightCompanion P b O hclosed hmin R → Prop}
    (hx : ∀ i t, C (weightCompanionX P b O hclosed hmin R i t))
    (hy : ∀ i t, C (weightCompanionY P b O hclosed hmin R i t))
    (hone : C 1) (hmul : ∀ g h, C g → C h → C (g*h))
    (hinv : ∀ g, C g → C g⁻¹) (g : WeightCompanion P b O hclosed hmin R) : C g := by
  rcases g with ⟨g,hg⟩
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with ⟨i,t,rfl⟩ | ⟨i,t,rfl⟩
    · exact hx i t
    · exact hy i t
  | one => exact hone
  | mul a c ha hc ih₁ ih₂ => exact hmul ⟨a,ha⟩ ⟨c,hc⟩ ih₁ ih₂
  | inv a ha ih => exact hinv ⟨a,ha⟩ ih
end Atlas.Chevalley

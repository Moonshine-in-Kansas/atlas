import Atlas.LinearGroups.Chevalley.WeightCompanionRootLaws

/-! Forgetting any chosen subfamily of actual simultaneous minuscule blocks.
The literal adjoint block and all pinned simple parameters are retained. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
variable {ι M N κ τ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] (e : τ → κ)

/-- Literal restriction of the family coordinates; no choice of word occurs. -/
def weightCompanionAmbientRestrict :
    WeightCompanionAmbient P b O R →* WeightCompanionAmbient P b (O ∘ e) R where
  toFun g := (g.1, fun a => g.2 (e a))
  map_one' := rfl
  map_mul' _ _ := rfl

theorem weightCompanionAmbientRestrict_mem {g : WeightCompanionAmbient P b O R}
    (hg : g ∈ weightCompanionSubgroup P b O hc hm R) :
    weightCompanionAmbientRestrict P b O R e g ∈
      weightCompanionSubgroup P b (O ∘ e) (fun a => hc (e a)) (fun a => hm (e a)) R := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨i,t,rfl⟩ | ⟨i,t,rfl⟩
    · exact Subgroup.subset_closure (Or.inl ⟨i,t,rfl⟩)
    · exact Subgroup.subset_closure (Or.inr ⟨i,t,rfl⟩)
  | one => simpa only [map_one] using
      (weightCompanionSubgroup P b (O ∘ e) (fun a => hc (e a)) (fun a => hm (e a)) R).one_mem
  | mul g h hg hh ihg ihh => simpa only [map_mul] using Subgroup.mul_mem _ ihg ihh
  | inv g hg ih => simpa only [map_inv] using Subgroup.inv_mem _ ih

def weightCompanionRestrict :
    WeightCompanion P b O hc hm R →*
      WeightCompanion P b (O ∘ e) (fun a => hc (e a)) (fun a => hm (e a)) R where
  toFun g := ⟨weightCompanionAmbientRestrict P b O R e g.val,
    weightCompanionAmbientRestrict_mem P b O hc hm R e g.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

@[simp] theorem weightCompanionRestrict_X (i : b.support) (t : R) :
    weightCompanionRestrict P b O hc hm R e (weightCompanionX P b O hc hm R i t) =
      weightCompanionX P b (O ∘ e) (fun a => hc (e a)) (fun a => hm (e a)) R i t := rfl

@[simp] theorem weightCompanionRestrict_Y (i : b.support) (t : R) :
    weightCompanionRestrict P b O hc hm R e (weightCompanionY P b O hc hm R i t) =
      weightCompanionY P b (O ∘ e) (fun a => hc (e a)) (fun a => hm (e a)) R i t := rfl

theorem weightCompanionRestrict_rho :
    (weightCompanionRho P b (O ∘ e) (fun a => hc (e a)) (fun a => hm (e a)) R).comp
      (weightCompanionRestrict P b O hc hm R e) = weightCompanionRho P b O hc hm R := by
  ext g
  rfl

/-- All retained simple generators have literal lifts, over every commutative ring. -/
theorem weightCompanionRestrict_surjective :
    Function.Surjective (weightCompanionRestrict P b O hc hm R e) := by
  intro g
  refine weightCompanion_induction P b (O ∘ e) (fun a => hc (e a))
    (fun a => hm (e a)) R
    (C := fun g => ∃ a, weightCompanionRestrict P b O hc hm R e a = g) ?_ ?_ ?_ ?_ ?_ g
  · intro i t
    exact ⟨weightCompanionX P b O hc hm R i t, rfl⟩
  · intro i t
    exact ⟨weightCompanionY P b O hc hm R i t, rfl⟩
  · exact ⟨1, map_one _⟩
  · rintro g h ⟨a,rfl⟩ ⟨c,rfl⟩
    exact ⟨a*c, map_mul _ _ _⟩
  · rintro g ⟨a,rfl⟩
    exact ⟨a⁻¹, map_inv _ _⟩

end Atlas.Chevalley
